'use strict';
/* ===== ユーティリティ ===== */
const $ = id => document.getElementById(id);
const rad = d => d * Math.PI / 180;
const gcd = (a, b) => b ? gcd(b, a % b) : a;
const rnd = a => a[Math.floor(Math.random() * a.length)];
const FN = { sin: '\\sin\\theta', cos: '\\cos\\theta', tan: '\\tan\\theta' };
const OP = { '=': '=', '>=': '\\geqq', '>': '>', '<=': '\\leqq', '<': '<' };
const SIDE = { '>=': '以上', '>': 'より大きい', '<=': '以下', '<': 'より小さい' };
const COORD = { sin: '点のy座標', cos: '点のx座標', tan: '接線 x＝1 上の高さ' };

/* 数式表示（KaTeX。読み込めない場合は簡易表示） */
function plain(s) {
  return s.replace(/\\frac\{([^{}]*)\}\{([^{}]*)\}/g, '($1)/($2)').replace(/\\sqrt\{([^{}]*)\}/g, '√$1')
    .replace(/\\circ/g, '°').replace(/\\theta/g, 'θ').replace(/\\pi/g, 'π').replace(/\\geqq/g, '≧').replace(/\\leqq/g, '≦')
    .replace(/\\approx/g, '≒').replace(/\\(sin|cos|tan)/g, '$1').replace(/\\(quad|,|\\ )/g, ' ').replace(/[{}]/g, '');
}
function tex(s) {
  if (window.katex) { try { return katex.renderToString(s, { throwOnError: false }); } catch (e) { /* 簡易表示へ */ } }
  return '<span>' + plain(s) + '</span>';
}

/* ===== 数学計算（角度は整数度で判定。解の範囲は 0°≦θ＜360°） ===== */
const BASE = {
  '0': ['0', 0], '1/2': ['\\frac{1}{2}', .5], '√2/2': ['\\frac{\\sqrt{2}}{2}', Math.SQRT1_2],
  '√3/2': ['\\frac{\\sqrt{3}}{2}', Math.sqrt(3) / 2], '1': ['1', 1],
  '√3/3': ['\\frac{\\sqrt{3}}{3}', Math.sqrt(3) / 3], '√3': ['\\sqrt{3}', Math.sqrt(3)]
};
function val(k) { const n = k[0] === '-', b = BASE[n ? k.slice(1) : k]; return { tex: (n ? '-' : '') + b[0], num: n ? -b[1] : b[1] }; }
function fval(f, d) {
  const r = rad(d);
  if (f === 'sin') return Math.sin(r);
  if (f === 'cos') return Math.cos(r);
  return Math.abs(Math.cos(r)) < 1e-9 ? NaN : Math.tan(r);
}
function sat(p, d) {
  const y = fval(p.f, d), v = p.v.num, e = 1e-9;
  if (isNaN(y)) return false;
  switch (p.op) {
    case '=': return Math.abs(y - v) < e;
    case '>=': return y >= v - e;
    case '>': return y > v + e;
    case '<=': return y <= v + e;
    default: return y < v - e;
  }
}
const LO = 0, HI = 360;
function eqSol(p) { const s = []; for (let d = LO; d < HI; d++) if (sat(p, d)) s.push(d); return s; }
function ineqSol(p) {
  const q = { ...p, op: '=' }, pts = [LO], out = [];
  for (let d = LO + 1; d < HI; d++) if (isNaN(fval(p.f, d)) || sat(q, d)) pts.push(d);
  const all = [...pts, HI];
  for (let i = 0; i < all.length - 1; i++) {
    const a = all[i], b = all[i + 1];
    if (!sat(p, (a + b) / 2)) continue;
    const last = out[out.length - 1];
    if (last && last.hi === a && sat(p, a)) last.hi = b; else out.push({ lo: a, hi: b });
  }
  out.forEach(u => { u.li = sat(p, u.lo); u.hiI = u.hi === HI ? false : sat(p, u.hi); });
  pts.forEach(b => { /* 1点だけの解（例：sinθ≧1） */
    if (!sat(p, b)) return;
    if (out.some(u => (b > u.lo || (b === u.lo && u.li)) && (b < u.hi || (b === u.hi && u.hiI)))) return;
    out.push({ lo: b, hi: b, li: true, hiI: true });
  });
  return out.sort((a, b) => a.lo - b.lo || a.hi - b.hi);
}
const solve = p => p.op === '=' ? eqSol(p).map(d => ({ lo: d, hi: d, li: true, hiI: true })) : ineqSol(p);
const isBoundary = (p, e) => isNaN(fval(p.f, e)) || sat({ ...p, op: '=' }, e);
const isAll = sol => sol.length === 1 && sol[0].lo === LO && sol[0].hi === HI && sol[0].li;

const SM = { 0: '0', 30: '\\frac{1}{2}', 45: '\\frac{\\sqrt{2}}{2}', 60: '\\frac{\\sqrt{3}}{2}', 90: '1' };
const TM = { 0: '0', 30: '\\frac{\\sqrt{3}}{3}', 45: '1', 60: '\\sqrt{3}' };
function exact(f, deg) {
  const d = ((deg % 360) + 360) % 360;
  if (d % 30 && d % 45) return null;
  const r = d <= 90 ? d : d <= 180 ? 180 - d : d <= 270 ? d - 180 : 360 - d;
  let mag, neg;
  if (f === 'sin') { mag = SM[r]; neg = d > 180; }
  else if (f === 'cos') { mag = SM[90 - r]; neg = d > 90 && d < 270; }
  else { if (d === 90 || d === 270) return 'undef'; mag = TM[r]; neg = (d > 90 && d < 180) || d > 270; }
  return neg && mag !== '0' ? '-' + mag : mag;
}

/* ===== 状態・問題 ===== */
const KEYS = { sin: ['-1', '-√3/2', '-√2/2', '-1/2', '0', '1/2', '√2/2', '√3/2', '1'], tan: ['-√3', '-1', '-√3/3', '0', '√3/3', '1', '√3'] };
KEYS.cos = KEYS.sin;
const REP = [0, 30, 45, 60, 90, 120, 135, 150, 180, 210, 225, 240, 270, 300, 315, 330, 360]; /* 代表角（度） */
const SNAP = 3; /* スナップする範囲（±度）。小さめにして動かしにくくならないようにする */

/* 「次の問題」用の候補（解が存在し、境界の扱いが明確なもの） */
const BANK = { eq: [], in: [] };
['sin', 'cos', 'tan'].forEach(f => KEYS[f].forEach(k => {
  const base = { f, k, v: val(k) };
  if (eqSol({ ...base, op: '=' }).length) BANK.eq.push({ f, op: '=', k });
  if (f !== 'tan' && Math.abs(base.v.num) === 1) return;
  ['>=', '>', '<=', '<'].forEach(op => {
    const s = ineqSol({ ...base, op });
    if (!s.length || s.some(u => u.lo === u.hi) || isAll(s)) return;
    BANK.in.push({ f, op, k });
  });
}));
const keyOf = q => q.f + q.op + q.k;
const hist = { eq: [], in: [] };
function pickNext(tab) {
  const list = BANK[tab].filter(q => !hist[tab].includes(keyOf(q)));
  const q = rnd(list.length ? list : BANK[tab]);
  hist[tab].push(keyOf(q)); if (hist[tab].length > 4) hist[tab].shift();
  return q;
}
const S = { tab: 'eq', rad: false, st: { eq: { f: 'sin', op: '=', k: '1/2', angle: 0, revealed: false }, in: { f: 'sin', op: '>=', k: '1/2', angle: 0, revealed: false } } };
const cur = () => S.st[S.tab];
const prob = st => ({ f: st.f, op: S.tab === 'eq' ? '=' : st.op, k: st.k, v: val(st.k) });

/* 角度の表記（度数法／弧度法）。内部の角度は常に度で持ち、表記だけを変える */
function angTex(d) {
  if (!S.rad) return d + '^\\circ';
  if (d === 0) return '0';
  const g = gcd(Math.abs(d), 180), n = d / g, m = 180 / g, an = Math.abs(n), top = an === 1 ? '\\pi' : an + '\\pi';
  return (n < 0 ? '-' : '') + (m === 1 ? top : `\\frac{${top}}{${m}}`);
}
function angPlain(d) {
  if (!S.rad) return d + '°';
  if (d === 0) return '0';
  const g = gcd(Math.abs(d), 180), n = d / g, m = 180 / g, an = Math.abs(n);
  return (n < 0 ? '−' : '') + (an === 1 ? 'π' : an + 'π') + (m === 1 ? '' : '/' + m);
}
const ivTex = u => u.lo === u.hi ? `\\theta=${angTex(u.lo)}` : `${angTex(u.lo)}${u.li ? '\\leqq' : '<'}\\theta${u.hiI ? '\\leqq' : '<'}${angTex(u.hi)}`;

/* ===== 描画 ===== */
const cv = $('cv'), ctx = cv.getContext('2d');
const W = 600, C = 300, R = 165;
const dpr = window.devicePixelRatio || 1;
cv.width = cv.height = W * dpr;
ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
const BLUE = '#1565c0', ORANGE = '#e65100', TEAL = '#00897b', RED = '#d32f2f';
const PX = d => C + R * Math.cos(rad(d)), PY = d => C - R * Math.sin(rad(d));

function dot(d, filled, col) {
  ctx.beginPath(); ctx.arc(PX(d), PY(d), 8, 0, 7);
  ctx.fillStyle = filled ? col : '#fff'; ctx.fill(); ctx.lineWidth = 3; ctx.strokeStyle = col; ctx.stroke();
}
function line(x1, y1, x2, y2, col, w, dash) {
  ctx.setLineDash(dash || []); ctx.lineWidth = w; ctx.strokeStyle = col;
  ctx.beginPath(); ctx.moveTo(x1, y1); ctx.lineTo(x2, y2); ctx.stroke(); ctx.setLineDash([]);
}
function text(s, x, y, col, size, align) {
  ctx.font = `bold ${size || 15}px sans-serif`; ctx.textAlign = align || 'center'; ctx.textBaseline = 'middle';
  ctx.lineWidth = 4; ctx.strokeStyle = '#fff'; ctx.strokeText(s, x, y); ctx.fillStyle = col; ctx.fillText(s, x, y);
}

function draw(st) {
  const p = prob(st), x = ctx, v = p.v.num, ineq = p.op !== '=', vlab = st.k.replace('-', '−');
  const sol = solve(p), show = st.revealed;
  x.clearRect(0, 0, W, W);
  /* 不等式：条件を満たす範囲は常に単位円上の弧で色付け（点Pの位置には左右されない） */
  if (ineq) sol.forEach(u => {
    if (u.lo === u.hi) return;
    x.beginPath(); x.moveTo(C, C); x.arc(C, C, R, -rad(u.lo), -rad(u.hi), true); x.closePath();
    x.fillStyle = 'rgba(21,101,192,.14)'; x.fill();
    x.beginPath(); x.arc(C, C, R, -rad(u.lo), -rad(u.hi), true); x.lineWidth = 9; x.strokeStyle = BLUE; x.stroke();
  });
  /* 座標軸と単位円 */
  line(20, C, W - 20, C, '#7a8591', 1.5); line(C, 20, C, W - 20, '#7a8591', 1.5);
  x.beginPath(); x.arc(C, C, R, 0, 7); x.lineWidth = 2; x.strokeStyle = '#37474f'; x.stroke();
  text('x', W - 14, C - 12, '#555', 14); text('y', C + 14, 16, '#555', 14); text('O', C - 12, C + 14, '#555', 14);
  text('1', C + R + 8, C + 14, '#555', 13); text('−1', C - R - 10, C + 14, '#555', 13);
  /* 基準線（右辺の値） */
  if (p.f === 'sin') {
    const yl = C - R * v;
    line(C - R - 40, yl, C + R + 40, yl, ORANGE, 2, [7, 5]); text('y＝' + vlab, 40, yl - 12, ORANGE, 14);
    text('1', C - 12, C - R - 8, '#555', 13); text('−1', C - 14, C + R + 10, '#555', 13);
  } else if (p.f === 'cos') {
    const xl = C + R * v;
    line(xl, C - R - 40, xl, C + R + 40, ORANGE, 2, [7, 5]); text('x＝' + vlab, xl + 4, 30, ORANGE, 14, 'left');
  } else {
    const yk = C - R * v, ext = 1.8 * R;
    line(C + R, 20, C + R, W - 20, '#8e6bbf', 2, [5, 5]); text('x＝1', C + R + 6, 30, '#6a4aa0', 14, 'left');
    line(C - ext, C + ext * v, C + ext, C - ext * v, ORANGE, 2, [7, 5]);
  }
  const cnt = {};
  const lab = d => { const m = ((d % 360) + 360) % 360, n = cnt[m] = (cnt[m] || 0) + 1, r = R + 28 + (n - 1) * 18; text(angPlain(d), C + r * Math.cos(rad(d)), C - r * Math.sin(rad(d)), '#222', 14); };
  if (ineq) {
    /* 境界の点：含む＝●、含まない＝○（0°と360°は同じ位置なので360°側には描かない） */
    const seen = new Set();
    sol.forEach(u => [[u.lo, u.li], [u.hi, u.hiI]].forEach(([e, f]) => {
      if (e === HI || seen.has(e) || !(u.lo === u.hi || isBoundary(p, e))) return;
      seen.add(e); dot(e, f, BLUE); if (show) lab(e);
    }));
  } else if (show) {
    /* 方程式：解答確認後に、解となる点をすべて表示（点Pとは色・形を変える） */
    sol.forEach(u => {
      line(C, C, PX(u.lo), PY(u.lo), ORANGE, 2);
      x.beginPath(); x.rect(PX(u.lo) - 9, PY(u.lo) - 9, 18, 18); x.fillStyle = 'rgba(230,81,0,.35)'; x.fill(); x.lineWidth = 4; x.strokeStyle = ORANGE; x.stroke();
      lab(u.lo);
    });
  }
  /* 現在の点P・半径と、選んだ関数に対応する補助線 */
  const a = st.angle, px = PX(a), py = PY(a), t = fval(p.f, a);
  if (p.f === 'sin') { line(px, py, px, C, TEAL, 5); x.fillStyle = TEAL; x.fillRect(px - 4, C - 4, 8, 8); }
  else if (p.f === 'cos') { line(px, py, C, py, TEAL, 5); x.fillStyle = TEAL; x.fillRect(C - 4, py - 4, 8, 8); }
  else if (!isNaN(t)) {
    const tv = R * Math.tan(rad(a)), k = Math.abs(tv) > 280 ? 280 / Math.abs(tv) : 1;
    line(px, py, C + R * k, C - tv * k, TEAL, 2, [4, 4]);
    line(C + R, C, C + R, C - tv * k, TEAL, 6);
    if (k === 1) { x.beginPath(); x.moveTo(C + R, C - tv - 8); x.lineTo(C + R + 8, C - tv); x.lineTo(C + R, C - tv + 8); x.lineTo(C + R - 8, C - tv); x.closePath(); x.fillStyle = TEAL; x.fill(); }
  }
  x.beginPath(); x.arc(C, C, 30, 0, -rad(a), a > 0); x.lineWidth = 3; x.strokeStyle = RED; x.stroke();
  text('θ', C + 50 * Math.cos(rad(a / 2)), C - 50 * Math.sin(rad(a / 2)), RED, 16);
  line(C, C, px, py, '#222', 5);
  x.beginPath(); x.arc(C, C, 4, 0, 7); x.fillStyle = '#222'; x.fill();
  x.beginPath(); x.arc(px, py, 12, 0, 7); x.fillStyle = RED; x.fill(); x.lineWidth = 3; x.strokeStyle = '#fff'; x.stroke();
  text('P', px + 20 * Math.cos(rad(a)), py - 20 * Math.sin(rad(a)), '#222', 15);
}

/* ===== 表示 ===== */
function valHtml(p, a) {
  const e = exact(p.f, a);
  if (e === 'undef') return `${tex(FN.tan)} は<b style="display:inline">定義されない</b>（cosθ＝0）`;
  if (e !== null) return tex(`${FN[p.f]}=${e}`);
  return tex(`${FN[p.f]}\\approx ${fval(p.f, a).toFixed(3)}`) + ' <small>（近似値）</small>';
}
function statusOf(st) {
  const p = prob(st), a = st.angle, und = isNaN(fval(p.f, a));
  if (p.op === '=') {
    if (und) return ['✖ tanθ は定義されない', false];
    return sat(p, a) ? ['✔ 現在の値は右辺と等しい', true] : ['✖ 現在の値は右辺と等しくない', false];
  }
  if (und) return ['✖ tanθ は定義されないので、条件を満たしていない', false];
  if (sat({ ...p, op: '=' }, a)) {
    const inc = p.op === '>=' || p.op === '<=';
    return [inc ? '◆ 境界上にある（等号を含むので、条件を満たしている）' : '◆ 境界上にある（等号を含まないので、条件を満たしていない）', inc];
  }
  return sat(p, a) ? ['✔ 条件を満たしている', true] : ['✖ 条件を満たしていない', false];
}
function explainHtml(st) {
  const p = prob(st), sol = solve(p), v = tex(p.v.tex), fn = tex(FN[p.f]);
  const guide = { sin: `直線 ${tex('y=' + p.v.tex)}`, cos: `直線 ${tex('x=' + p.v.tex)}`, tan: `高さ ${v} の点と原点を結ぶ直線` }[p.f];
  const note = '<li>θ＝360° は 0° と同じ位置なので、範囲は 0°≦θ＜360° で考えます。</li>';
  if (p.op === '=') {
    if (!sol.length) return `<b>解</b><div class="line">解なし</div>`;
    return `<b>解</b><div class="line">${tex('\\theta=' + sol.map(u => angTex(u.lo)).join(',\\ '))}</div>
      <b>考え方</b><ol><li>${fn}＝${v} は、単位円上で${COORD[p.f]}が ${v} になる点を探す問題です。</li>
      <li>${guide}と単位円の交点が解です。${p.f === 'tan' ? '原点を通る直線なので、解は180°ずつ離れた点になります。' : ''}</li>${note}</ol>`;
  }
  const bd = eqSol({ ...p, op: '=' }), inc = p.op === '>=' || p.op === '<=';
  const range = !sol.length ? '<div class="line">解なし</div>'
    : isAll(sol) ? `<div class="line">${tex(ivTex(sol[0]))}</div><div>（すべての角度が解）</div>`
      : sol.map(u => `<div class="line">${tex(ivTex(u))}</div>`).join('');
  return `<b>解の範囲</b>${range}<b>考え方</b><ol>
    <li>まず境界を求めます。${fn}＝${v} となる角度は ${bd.length ? tex(bd.map(d => angTex(d)).join(',\\ ')) : 'ありません'}。${p.f === 'tan' ? 'また、tanθ は 90°、270° では定義されないので、解に含みません。' : ''}</li>
    <li>${COORD[p.f]}が ${v} ${SIDE[p.op]}となる部分が、青く色付けされた範囲です。</li>
    <li>${tex(OP[p.op])} なので境界は${inc ? '含みます（●）' : '含みません（○）'}。</li>${note}</ol>`;
}
function fillRhs(st) {
  $('rhs').innerHTML = KEYS[st.f].map(k => `<option value="${k}">${k.replace('-', '−')}</option>`).join('');
  $('rhs').value = st.k;
}
function render() {
  const st = cur(), p = prob(st), eq = S.tab === 'eq';
  document.querySelectorAll('[data-tab]').forEach(b => b.setAttribute('aria-selected', b.dataset.tab === S.tab));
  document.querySelectorAll('[data-rad]').forEach(b => b.setAttribute('aria-pressed', (b.dataset.rad === '1') === S.rad));
  document.querySelectorAll('[data-f]').forEach(b => b.setAttribute('aria-pressed', b.dataset.f === st.f));
  $('opWrap').hidden = eq; $('op').value = st.op;
  if ($('rhs').dataset.f !== st.f + S.tab) { fillRhs(st); $('rhs').dataset.f = st.f + S.tab; }
  $('rhs').value = st.k;
  $('problem').innerHTML = `${tex(FN[p.f] + OP[p.op] + p.v.tex)}<small>ただし、${tex(angTex(LO) + '\\leqq\\theta<' + angTex(HI))} とする。</small>`;
  $('angleOut').innerHTML = tex('\\theta=' + angTex(st.angle)) + (st.angle === 360 ? ' <small>（0°と同じ位置）</small>' : '');
  $('valOut').innerHTML = '現在：' + valHtml(p, st.angle);
  $('rhsOut').innerHTML = eq ? '右辺：' + tex(p.v.tex) : '';
  const [msg, good] = statusOf(st);
  $('status').textContent = msg; $('status').style.color = good ? '#1b7f3b' : '#b3261e';
  $('slider').value = st.angle;
  if (document.activeElement !== $('angIn')) {
    const g = gcd(st.angle, 180);
    $('angIn').value = !S.rad ? st.angle : st.angle === 0 ? '0' : (st.angle / g) + (180 / g === 1 ? '' : '/' + (180 / g));
  }
  $('angUnit').textContent = S.rad ? 'π' : '°';
  document.querySelectorAll('[data-step]').forEach(b => { const s = +b.dataset.step; b.textContent = (s < 0 ? '−' : '＋') + angPlain(Math.abs(s)); });
  $('solBox').hidden = !st.revealed;
  $('solBox').innerHTML = st.revealed ? explainHtml(st) : '';
  $('revealBtn').disabled = st.revealed;
  draw(st);
}

/* ===== 角度の操作 ===== */
function setAngle(a) { if (isNaN(a)) return; cur().angle = Math.max(0, Math.min(360, Math.round(a))); render(); }
let drag = false;
function move(e) {
  const r = cv.getBoundingClientRect(), k = W / r.width;
  const x = (e.clientX - r.left) * k - C, y = C - (e.clientY - r.top) * k;
  if (Math.hypot(x, y) < 8) return;
  let b = ((Math.round(Math.atan2(y, x) * 180 / Math.PI) % 360) + 360) % 360;
  const s = REP.reduce((m, d) => Math.abs(d - b) < Math.abs(m - b) ? d : m, REP[0]);
  if (Math.abs(s - b) <= SNAP) b = s; /* 代表角の近くだけスナップ。それ以外は自由 */
  setAngle(b);
}
cv.addEventListener('pointerdown', e => { drag = true; cv.setPointerCapture(e.pointerId); move(e); e.preventDefault(); });
cv.addEventListener('pointermove', e => { if (drag) { move(e); e.preventDefault(); } });
['pointerup', 'pointercancel'].forEach(t => cv.addEventListener(t, () => { drag = false; }));
cv.addEventListener('keydown', e => {
  const k = { ArrowRight: 1, ArrowUp: 1, ArrowLeft: -1, ArrowDown: -1 }[e.key];
  if (!k) return; e.preventDefault(); setAngle(cur().angle + k * (e.shiftKey ? 15 : 1));
});
$('slider').addEventListener('input', e => setAngle(+e.target.value));
document.querySelectorAll('[data-step]').forEach(b => b.addEventListener('click', () => setAngle(cur().angle + +b.dataset.step)));
function applyInput() {
  const s = $('angIn').value.replace(/[π°度\s]/g, '').replace(/[−ー]/g, '-');
  const [n, m] = s.split('/');
  let v = s.startsWith('/') ? 1 : n === '-' ? -1 : n === '' ? NaN : parseFloat(n);
  if (m !== undefined) v = v / parseFloat(m);
  if (S.rad) v *= 180;
  if (isNaN(v)) { render(); return; }
  setAngle(v);
}
$('angSet').addEventListener('click', applyInput);
$('angIn').addEventListener('keydown', e => { if (e.key === 'Enter') applyInput(); });
$('angIn').addEventListener('blur', render);

/* ===== 問題の選択・ボタン ===== */
function changeProblem(patch) { Object.assign(cur(), patch, { angle: 0, revealed: false }); render(); }
document.querySelectorAll('[data-f]').forEach(b => b.addEventListener('click', () => {
  const f = b.dataset.f, k = KEYS[f].includes(cur().k) ? cur().k : (f === 'tan' ? '1' : '1/2');
  changeProblem({ f, k });
}));
$('op').addEventListener('change', e => changeProblem({ op: e.target.value }));
$('rhs').addEventListener('change', e => changeProblem({ k: e.target.value }));
document.querySelectorAll('[data-tab]').forEach(b => b.addEventListener('click', () => { S.tab = b.dataset.tab; render(); }));
document.querySelectorAll('[data-rad]').forEach(b => b.addEventListener('click', () => { S.rad = b.dataset.rad === '1'; render(); }));
$('nextBtn').addEventListener('click', () => { const q = pickNext(S.tab); changeProblem({ f: q.f, op: q.op === '=' ? cur().op : q.op, k: q.k }); });
$('revealBtn').addEventListener('click', () => { cur().revealed = true; render(); });
$('resetBtn').addEventListener('click', () => { const st = cur(); st.angle = 0; st.revealed = false; render(); });

/* ===== 操作ガイド ===== */
function showGuide(on) { $('modal').hidden = !on; (on ? $('closeGuide') : $('guideBtn')).focus(); }
$('guideBtn').addEventListener('click', () => showGuide(true));
$('closeGuide').addEventListener('click', () => showGuide(false));
$('modal').addEventListener('click', e => { if (e.target === $('modal')) showGuide(false); });
document.addEventListener('keydown', e => { if (e.key === 'Escape' && !$('modal').hidden) showGuide(false); });

render();
