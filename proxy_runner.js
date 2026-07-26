const fs = require('fs');
const path = require('path');
const os = require('os');
const { spawn } = require('child_process');
const crypto = require('crypto');
const axios = require('axios');
const FormData = require('form-data');
const {
    normalizeTimeoutMinutes,
    runChildWithTimeout,
    DEFAULT_GRACEFUL_TERMINATION_MS
} = require('./lib/runtime_helpers');
const { sendTelegramNotification } = require('./lib/telegram');

const ACTION_TIMEOUT_MINUTES = normalizeTimeoutMinutes(process.env.ACTION_TIMEOUT_MINUTES);
const ACTION_TIMEOUT_MS = ACTION_TIMEOUT_MINUTES * 60 * 1000;
const TG_BOT_TOKEN = process.env.TG_BOT_TOKEN;
const TG_CHAT_ID = process.env.TG_CHAT_ID;

// --- 退出码（与 action_renew.js 完全一致） ---
const EXIT_CODE = {
    SUCCESS: 0,
    FATAL: 1,
    PROXY_RETRY: 42,       // 只有这个码才触发代理轮换
    RENEW_CAPTCHA_FAILED: 43, // Renew ALTCHA 失败，不换代理
    NOT_READY: 3,
    ALREADY_RENEWED: 4,
    LOGIN_FAILED: 5,
    NO_PROXY_AVAILABLE: 6 // 全部代理冷却，暂无可用代理
};

// --- 只有明确成功/不可重试状态才停止轮换 ---
const NON_RETRYABLE = new Set([
    EXIT_CODE.SUCCESS,
    EXIT_CODE.NOT_READY,
    EXIT_CODE.ALREADY_RENEWED,
    EXIT_CODE.LOGIN_FAILED,
    EXIT_CODE.RENEW_CAPTCHA_FAILED
]);

const CONFIG = {
    MAX_PROXY_SWITCHES: 5,
    COOLDOWN_FILE: path.join(process.cwd(), 'proxy-cooldown.json'),
    COOLDOWN_HOURS: 24,
    PROXIES_FILE: path.join(process.cwd(), 'proxies.txt')
};

function createAttemptResultFile(attempt) {
    const nonce = crypto.randomBytes(8).toString('hex');
    return path.join(os.tmpdir(), `katabump-action-result-${process.pid}-${attempt}-${nonce}.json`);
}

function readActionResult(resultFile) {
    if (!resultFile) return null;
    try {
        if (!fs.existsSync(resultFile)) return null;
        const parsed = JSON.parse(fs.readFileSync(resultFile, 'utf-8'));
        return parsed && typeof parsed === 'object' ? parsed : null;
    } catch (error) {
        console.error('[proxy-runner] 本次代理结果文件读取失败:', error.message);
        return null;
    } finally {
        try { fs.unlinkSync(resultFile); } catch (error) { }
    }
}

function actionStatusFromCode(code) {
    switch (code) {
        case EXIT_CODE.SUCCESS: return 'success';
        case EXIT_CODE.NOT_READY: return 'not_ready';
        case EXIT_CODE.ALREADY_RENEWED: return 'already_renewed';
        case EXIT_CODE.LOGIN_FAILED: return 'login_failed';
        case EXIT_CODE.RENEW_CAPTCHA_FAILED: return 'captcha_required';
        case EXIT_CODE.PROXY_RETRY: return 'proxy_retry';
        default: return 'error';
    }
}

function makeAttemptRecord(attempt, parsed, childResult) {
    const actionResult = childResult.actionResult || {};
    const code = Number.isInteger(actionResult.exitCode) ? actionResult.exitCode : childResult.code;
    return {
        attempt,
        proxy: parsed ? safeProxyId(parsed) : 'direct',
        code,
        status: actionResult.status || actionStatusFromCode(code),
        message: actionResult.message || childResult.error?.message || (childResult.timedOut ? 'action_renew.js timed out' : ''),
        screenshotPath: actionResult.screenshotPath || null,
        htmlPath: actionResult.htmlPath || null,
        accounts: Array.isArray(actionResult.accounts) ? actionResult.accounts : [],
        timedOut: childResult.timedOut === true
    };
}

function buildFinalSummary(finalCode, finalResult, attempts) {
    const lastAttempt = attempts.length > 0 ? attempts[attempts.length - 1] : null;
    const actionResult = finalResult || lastAttempt || {};
    let status = actionResult.status || actionStatusFromCode(finalCode);
    if (finalCode === EXIT_CODE.NO_PROXY_AVAILABLE) status = 'no_proxy_available';
    if (finalCode === EXIT_CODE.FATAL && attempts.length > 0 && attempts.every(item => item.code === EXIT_CODE.PROXY_RETRY)) {
        status = 'proxy_exhausted';
    }
    let message = actionResult.message || '';
    if (!message) {
        message = status === 'proxy_exhausted' ? 'All proxy attempts returned PROXY_RETRY' : '';
    }
    return { status, message, attempts };
}

function formatFinalNotification(finalCode, finalResult, attempts) {
    const summary = buildFinalSummary(finalCode, finalResult, attempts);
    const lines = [];
    lines.push(`[Katabump Renew] ${summary.status}`);
    lines.push('');
    for (const item of attempts) {
        const time = new Date().toISOString();
        lines.push(`[${item.attempt}] proxy=${item.proxy} code=${item.code} status=${item.status} ${item.message || ''}`);
    }
    lines.push('');
    lines.push(`Final: ${summary.status} — ${summary.message}`);
    return lines.join('\n');
}

// ============================================================
//  冷却管理
// ============================================================
function proxyKey(parsed) {
    return `${parsed.host}:${parsed.port}`;
}

function safeProxyId(parsed) {
    if (!parsed) return 'direct';
    const host = parsed.host || '';
    const port = parsed.port || '';
    const masked = host.split('.').map((seg, i) => i === 0 || i === 3 ? seg : '***');
    return `${masked.join('.')}:${port}`;
}

function loadCooldowns() {
    try {
        if (!fs.existsSync(CONFIG.COOLDOWN_FILE)) return {};
        const raw = fs.readFileSync(CONFIG.COOLDOWN_FILE, 'utf-8');
        return JSON.parse(raw);
    } catch (e) {
        console.log('[proxy-runner] 冷却文件读取失败，视为无冷却:', e.message);
        return {};
    }
}

function saveCooldowns(cooldowns) {
    try {
        fs.writeFileSync(CONFIG.COOLDOWN_FILE, JSON.stringify(cooldowns, null, 2), 'utf-8');
    } catch (e) {
        console.error('[proxy-runner] 保存冷却文件失败:', e.message);
    }
}

function addCooldown(cooldowns, proxyKey, reason) {
    const until = Math.floor(Date.now() / 1000) + CONFIG.COOLDOWN_HOURS * 3600;
    cooldowns[proxyKey] = { until, reason };
    saveCooldowns(cooldowns);
    console.log(`[proxy-runner] 代理 ${proxyKey} 加入冷却，持续 ${CONFIG.COOLDOWN_HOURS}h，原因: ${reason}`);
}

function removeExpiredCooldowns(cooldowns) {
    const now = Math.floor(Date.now() / 1000);
    let removed = 0;
    for (const key of Object.keys(cooldowns)) {
        if (cooldowns[key].until <= now) {
            delete cooldowns[key];
            removed++;
        }
    }
    if (removed > 0) {
        saveCooldowns(cooldowns);
        console.log(`[proxy-runner] 已清理 ${removed} 条过期冷却`);
    }
}

// ============================================================
//  代理解析（唯一真相源）
// ============================================================
function parseProxyLine(line, lineNumber) {
    const trimmed = (line || '').trim();
    if (!trimmed || trimmed.startsWith('#')) return { valid: false, reason: 'empty_or_comment', lineNumber };

    const isValidPort = (s) => /^[0-9]+$/.test(s) && s.length > 0 && s.length <= 5 && Number(s) >= 1 && Number(s) <= 65535;
    const isValidHost = (s) => (
        typeof s === 'string' &&
        s.length > 0 &&
        !/[\\s/\\\\?#@\u0000-\u001f\u007f]/.test(s)
    );

    // Format 1: http://USER:PASSWORD@HOST:PORT
    if (trimmed.startsWith('http://')) {
        let parsedUrl;
        try {
            parsedUrl = new URL(trimmed);
        } catch {
            return { valid: false, reason: 'invalid_url_format', lineNumber };
        }

        // URL format is exactly http://USERNAME:PASSWORD@HOST:PORT.
        // URL accepts paths, queries, and fragments, but none are part of the
        // frozen proxy input format. A trailing extra host field is rejected by
        // Node.js URL parser, so we only accept URL with port and no path/query/fragment.
        // If the URL has a path, query, or fragment, or does not have a port, reject.
        if (!parsedUrl.port || parsedUrl.pathname !== '/' || parsedUrl.search || parsedUrl.hash) {
            return { valid: false, reason: 'invalid_url_format', lineNumber };
        }

        const host = parsedUrl.hostname;
        if (!isValidHost(host)) {
            return { valid: false, reason: 'invalid_host', lineNumber };
        }

        const port = parsedUrl.port;
        if (!isValidPort(port)) {
            return { valid: false, reason: 'invalid_port', lineNumber };
        }

        const username = parsedUrl.username ? decodeURIComponent(parsedUrl.username) : '';
        const password = parsedUrl.password ? decodeURIComponent(parsedUrl.password) : '';

        // Auth is required for Webshare-style proxies
        if (!username || !password) {
            return { valid: false, reason: 'missing_auth_for_webshare', lineNumber };
        }

        return {
            valid: true,
            protocol: 'http',
            host,
            port,
            username,
            password,
            lineNumber
        };
    }

    // Format 2: IP:PORT:USER:PASS
    const parts = trimmed.split(':');
    if (parts.length === 4) {
        const [host, port, username, password] = parts;
        if (!isValidHost(host)) return { valid: false, reason: 'invalid_host', lineNumber };
        if (!isValidPort(port)) return { valid: false, reason: 'invalid_port', lineNumber };
        if (!username) return { valid: false, reason: 'missing_username', lineNumber };
        if (!password) return { valid: false, reason: 'missing_password', lineNumber };
        return { valid: true, protocol: 'http', host, port, username, password, lineNumber };
    }

    // Format 3: IP:PORT (no auth)
    if (parts.length === 2) {
        const [host, port] = parts;
        if (!isValidHost(host)) return { valid: false, reason: 'invalid_host', lineNumber };
        if (!isValidPort(port)) return { valid: false, reason: 'invalid_port', lineNumber };
        return { valid: true, protocol: 'http', host, port, username: '', password: '', lineNumber };
    }

    return { valid: false, reason: 'unsupported_format', lineNumber };
}

function buildHttpProxy(parsed) {
    if (!parsed || !parsed.valid) return null;
    const { protocol, host, port, username, password } = parsed;
    if (username && password) {
        return `${protocol}://${encodeURIComponent(username)}:${encodeURIComponent(password)}@${host}:${port}`;
    }
    return `${protocol}://${host}:${port}`;
}

function maskProxyUrl(url) {
    if (!url) return 'null';
    try {
        const u = new URL(url);
        if (u.username) u.username = '***';
        if (u.password) u.password = '***';
        return u.toString();
    } catch {
        return '(invalid)';
    }
}

function emitGithubMask(parsed) {
    if (!parsed || !parsed.valid) return;
    const key = proxyKey(parsed);
    if (process.env.GITHUB_ACTIONS === 'true' && process.env.GITHUB_ENV) {
        try {
            fs.appendFileSync(process.env.GITHUB_ENV, `MASKED_PROXY_KEY=${key}\n`);
        } catch (e) {
            // ignore
        }
    }
}

function buildChildEnv(parsed, parentEnv) {
    const env = { ...parentEnv };
    if (parsed === null) {
        delete env.HTTP_PROXY;
        delete env.HTTPS_PROXY;
        delete env.http_proxy;
        delete env.https_proxy;
        return env;
    }
    if (!parsed || !parsed.valid) return null;
    const proxyUrl = buildHttpProxy(parsed);
    if (!proxyUrl) return null;
    env.HTTP_PROXY = proxyUrl;
    env.HTTPS_PROXY = proxyUrl;
    env.http_proxy = proxyUrl;
    env.https_proxy = proxyUrl;
    // 传递当前代理标识给子进程，用于截图文件名
    env.CURRENT_PROXY = proxyKey(parsed);
    return env;
}

// ============================================================
//  加载代理列表
// ============================================================
function loadProxies() {
    if (!fs.existsSync(CONFIG.PROXIES_FILE)) {
        console.log('[proxy-runner] proxies.txt 不存在，直接运行（无代理）');
        return { configured: false, valid: [], invalidCount: 0 };
    }
    const raw = fs.readFileSync(CONFIG.PROXIES_FILE, 'utf-8');
    const lines = raw.split('\n');
    const nonEmptyLines = [];
    for (let origIdx = 0; origIdx < lines.length; origIdx++) {
        const trimmed = lines[origIdx].trim();
        if (trimmed && !trimmed.startsWith('#')) {
            nonEmptyLines.push({ trimmed, lineNumber: origIdx + 1 });
        }
    }
    const valid = [];
    const invalid = [];
    for (const { trimmed, lineNumber } of nonEmptyLines) {
        const parsed = parseProxyLine(trimmed, lineNumber);
        if (parsed.valid && buildHttpProxy(parsed)) {
            valid.push(parsed);
        } else {
            if (parsed.valid) parsed.reason = 'invalid_proxy_url';
            invalid.push(parsed);
        }
    }
    for (const p of invalid) {
        console.log(`[proxy-runner] 第 ${p.lineNumber} 行无效：${p.reason}`);
    }
    console.log(`[proxy-runner] proxies.txt 共 ${valid.length} 条有效代理`);
    return { configured: true, valid, invalidCount: invalid.length };
}

function selectRandomProxy(proxies, cooldowns) {
    const now = Math.floor(Date.now() / 1000);
    const available = [];
    for (const parsed of proxies) {
        const key = proxyKey(parsed);
        if (!cooldowns[key] || cooldowns[key].until <= now) {
            available.push(parsed);
        }
    }

    if (available.length === 0) {
        console.log('[proxy-runner] 无可选代理（全部冷却中），本轮停止，不清空冷却名单');
        return null;
    }

    const parsed = available[crypto.randomInt(available.length)];
    console.log(`[proxy-runner] 选择代理: ${safeProxyId(parsed)}`);
    return parsed;
}

// ============================================================
//  运行子进程
// ============================================================
async function runActionRenew(parsed, attempt = 1) {
    const env = buildChildEnv(parsed, process.env);
    if (!env) {
        console.error('[proxy-runner] 当前代理格式无效，不静默直连');
        return { code: EXIT_CODE.FATAL, timedOut: false, actionResult: null };
    }

    if (parsed === null) {
        console.log('[proxy-runner] 无代理模式，已清除 HTTP_PROXY / HTTPS_PROXY');
    } else {
        console.log(`[proxy-runner] 设置 HTTP_PROXY=${safeProxyId(parsed)}`);
        const proxyUrl = buildHttpProxy(parsed);
        console.log(`[proxy-runner] 代理地址: ${maskProxyUrl(proxyUrl)}`);
    }

    const resultFile = createAttemptResultFile(attempt);
    const child = spawn('node', ['action_renew.js', '--result-file', resultFile], {
        env,
        stdio: ['inherit', 'inherit', 'inherit'],
        cwd: process.cwd()
    });

    try {
        const childResult = await runChildWithTimeout(child, ACTION_TIMEOUT_MS, DEFAULT_GRACEFUL_TERMINATION_MS);
        return {
            code: childResult.code,
            timedOut: childResult.timedOut,
            actionResult: readActionResult(resultFile)
        };
    } catch (error) {
        try { fs.unlinkSync(resultFile); } catch (cleanupError) { }
        return { code: EXIT_CODE.FATAL, timedOut: false, actionResult: null, error };
    }
}

// ============================================================
//  finalizeWorkflow 和日志输出
// ============================================================
function finalizeWorkflow(finalCode, finalResult, attempts) {
    const summary = buildFinalSummary(finalCode, finalResult, attempts);
    console.log(`\n[proxy-runner] ===== 最终结果 =====`);
    console.log(`[proxy-runner] 最终状态: ${summary.status}`);
    console.log(`[proxy-runner] 详细信息: ${summary.message}`);
    for (const item of attempts) {
        const time = new Date().toISOString();
        console.log(`[proxy-runner]   [${item.attempt}] proxy=${item.proxy} code=${item.code} status=${item.status} ${item.message || ''}`);
    }
    console.log('');
    return finalCode;
}

// ============================================================
//  主流程
// ============================================================
async function runProxyWorkflow(attempts) {
    console.log(`[proxy-runner] 启动代理轮换控制器`);
    console.log(`[proxy-runner] 最多尝试 ${CONFIG.MAX_PROXY_SWITCHES} 个代理，冷却 ${CONFIG.COOLDOWN_HOURS}h`);
    console.log(`[proxy-runner] 退出码映射: SUCCESS=0 FATAL=1 PROXY_RETRY=42 NOT_READY=3 ALREADY_RENEWED=4 LOGIN_FAILED=5 NO_PROXY_AVAILABLE=6 RENEW_CAPTCHA_FAILED=43`);

    const proxyResult = loadProxies();
    const proxies = proxyResult.valid;
    let cooldowns = loadCooldowns();
    removeExpiredCooldowns(cooldowns);

    // ===== 先尝试直连（无代理） =====
    console.log(`\n[proxy-runner] ===== 尝试直连 =====`);
    const directResult = await runActionRenew(null, 1);
    const directAttempt = makeAttemptRecord(1, null, directResult);
    attempts.push(directAttempt);

    if (NON_RETRYABLE.has(directResult.code)) {
        const normalizedCode = (directResult.code === EXIT_CODE.NOT_READY || directResult.code === EXIT_CODE.ALREADY_RENEWED) ? EXIT_CODE.SUCCESS : directResult.code;
        if (directResult.code !== normalizedCode) {
            console.log(`[proxy-runner] 业务状态码 ${directResult.code} 归一为 ${normalizedCode}（正常业务，非失败）`);
        }
        console.log(`[proxy-runner] 直连成功，退出码 ${normalizedCode}`);
        return finalizeWorkflow(normalizedCode, directResult.actionResult || directAttempt, attempts);
    }

    if (directResult.code === EXIT_CODE.FATAL) {
        console.log(`[proxy-runner] 直连 FATAL，非代理问题，停止`);
        return finalizeWorkflow(EXIT_CODE.FATAL, directResult.actionResult || directAttempt, attempts);
    }

    // 直连返回 PROXY_RETRY → 降级到代理
    console.log(`[proxy-runner] 直连失败 (PROXY_RETRY)，降级到代理...`);

    // 如果没有可用代理，直接报错
    if (proxies.length === 0) {
        console.log('[proxy-runner] 直连失败，且无可用代理，停止');
        return finalizeWorkflow(EXIT_CODE.NO_PROXY_AVAILABLE, {
            status: 'no_proxy_available',
            message: 'Direct connection failed and no proxies available',
            accounts: []
        }, attempts);
    }

    for (let attempt = 2; attempt <= CONFIG.MAX_PROXY_SWITCHES + 1; attempt++) {
        console.log(`\n[proxy-runner] ===== 代理尝试 ${attempt - 1}/${CONFIG.MAX_PROXY_SWITCHES} =====`);

        // 1) 选代理
        let selection = null;

        if (proxies.length > 0) {
            selection = selectRandomProxy(proxies, cooldowns);
            if (!selection) {
                console.log('[proxy-runner] 无可选代理（全部冷却中），本轮停止，不清空冷却名单');
                return finalizeWorkflow(EXIT_CODE.NO_PROXY_AVAILABLE, {
                    status: 'no_proxy_available',
                    message: 'No proxy is currently available',
                    accounts: []
                }, attempts);
            }
        } else if (proxyResult.configured) {
            console.log('[proxy-runner] proxies.txt 存在但无有效代理，禁止静默直连');
            return finalizeWorkflow(EXIT_CODE.NO_PROXY_AVAILABLE, {
                status: 'no_proxy_available',
                message: 'No valid proxy is configured',
                accounts: []
            }, attempts);
        } else {
            console.log('[proxy-runner] 未配置 proxies.txt，无代理直连');
        }

        // 2) 跑业务脚本；子进程由 action_renew.js 自己管理 BrowserContext/Browser 生命周期。
        const result = await runActionRenew(selection || null, attempt);
        const code = result.code;
        const attemptRecord = makeAttemptRecord(attempt, selection, result);
        attempts.push(attemptRecord);

        // 3) 按退出码决定
        if (NON_RETRYABLE.has(code)) {
            // NOT_READY(3) 和 ALREADY_RENEWED(4) 是正常业务状态，归一为 0 避免 GitHub Actions 显示失败
            const normalizedCode = (code === EXIT_CODE.NOT_READY || code === EXIT_CODE.ALREADY_RENEWED) ? EXIT_CODE.SUCCESS : code;
            if (code !== normalizedCode) {
                console.log(`[proxy-runner] 业务状态码 ${code} 归一为 ${normalizedCode}（正常业务，非失败）`);
            }
            console.log(`[proxy-runner] 不可重试退出码 ${normalizedCode}，结束本轮`);
            return finalizeWorkflow(normalizedCode, result.actionResult || attemptRecord, attempts);
        }

        if (code === EXIT_CODE.PROXY_RETRY && selection) {
            const parsed = selection;
            const key = proxyKey(parsed);
            addCooldown(cooldowns, key, 'proxy_retry_from_action_renew');
            cooldowns = loadCooldowns();
            console.log(`[proxy-runner] 选择下一个代理`);
            continue;
        }

        if (code === EXIT_CODE.FATAL) {
            console.log(`[proxy-runner] 退出码 1 (FATAL)，非代理问题，停止`);
            return finalizeWorkflow(EXIT_CODE.FATAL, result.actionResult || attemptRecord, attempts);
        }

        // 未知退出码也停止（不是 PROXY_RETRY）
        console.log(`[proxy-runner] 未知退出码 ${code}，不换代理，停止`);
        return finalizeWorkflow(code, result.actionResult || attemptRecord, attempts);
    }

    console.log(`[proxy-runner] 已尝试 ${CONFIG.MAX_PROXY_SWITCHES} 个代理，均未成功`);
    return finalizeWorkflow(EXIT_CODE.FATAL, attempts[attempts.length - 1] || {
        status: 'proxy_exhausted',
        message: 'All proxy attempts returned PROXY_RETRY',
        accounts: []
    }, attempts);
}

async function main() {
    const attempts = [];
    try {
        return await runProxyWorkflow(attempts);
    } catch (error) {
        console.error('[proxy-runner] 主流程异常:', error.message);
        return finalizeWorkflow(EXIT_CODE.FATAL, {
            status: 'error',
            message: error.message,
            accounts: []
        }, attempts);
    }
}

if (process.argv[1] && path.resolve(process.argv[1]) === path.resolve(__filename)) {
    main()
        .then((code) => process.exit(code))
        .catch((e) => {
            console.error(e);
            process.exit(EXIT_CODE.FATAL);
        });
}

module.exports = {
    parseProxyLine,
    buildHttpProxy,
    buildChildEnv,
    maskProxyUrl,
    emitGithubMask,
    finalizeWorkflow,
    makeAttemptRecord,
    buildFinalSummary,
    formatFinalNotification,
    loadProxies,
    selectRandomProxy,
    proxyKey,
    safeProxyId,
    runActionRenew,
    readActionResult,
    makeAttemptRecord,
    buildFinalSummary,
    formatFinalNotification,
    normalizeTimeoutMinutes,
    runChildWithTimeout,
    ACTION_TIMEOUT_MINUTES,
    ACTION_TIMEOUT_MS,
    DEFAULT_GRACEFUL_TERMINATION_MS
};