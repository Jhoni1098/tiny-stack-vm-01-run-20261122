import { readdirSync, readFileSync, mkdirSync, writeFileSync } from "node:fs";

const OUT_MAX = 65536;
const STEP_MAX = 1000000;

// Opcode byte -> immediate length, or -1 for an unknown opcode. One table read
// replaces the per-step validity chain and length ternary in the hot loop.
const IMM = new Int8Array(256).fill(-1);
for (const b of [0, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 48, 49, 50, 51, 52, 64, 65, 80, 81, 82, 83]) IMM[b] = 0;
IMM[1] = 1; IMM[2] = 4; IMM[48] = IMM[49] = IMM[50] = IMM[51] = 2;

// Run one program on its input. Returns { e: exit code, o: output bytes }.
function run(p, g) {
  const n = p.length;
  const D = new Int32Array(256); // data stack
  let sp = 0;
  const C = new Int32Array(64); // call stack
  let cp = 0;
  const M = new Int32Array(256); // memory
  const o = new Uint8Array(OUT_MAX);
  let ol = 0;
  let ip = 0; // input position
  let pc = 0;
  let st = 0; // steps executed
  const end = (e) => ({ e, o: o.slice(0, ol) });

  for (;;) {
    if (st === STEP_MAX) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const b = p[pc];
    if (b === 1) { // PUSH8 fast path: 29% of practice steps
      if (pc + 1 >= n) return end(9);
      if (sp > 255) return end(3);
      D[sp++] = (p[pc + 1] << 24) >> 24;
      pc += 2;
      st++;
      continue;
    }
    if (b === 48) { // JMP fast path: 15% of practice steps
      if (pc + 2 >= n) return end(9);
      pc += 3 + (((p[pc + 1] | (p[pc + 2] << 8)) << 16) >> 16);
      st++;
      continue;
    }
    const m = IMM[b];
    if (m < 0) return end(5); // unknown opcode
    if (pc + m >= n) return end(9);
    st++;
    pc += 1 + m; // pc now points past the instruction (the "next" address)
    switch (b) {
      case 0: // HALT
        return end(0);
      case 1: // PUSH8, sign-extended
        if (sp > 255) return end(3);
        D[sp++] = (p[pc - 1] << 24) >> 24;
        break;
      case 2: // PUSH32, little-endian
        if (sp > 255) return end(3);
        D[sp++] = p[pc - 4] | (p[pc - 3] << 8) | (p[pc - 2] << 16) | (p[pc - 1] << 24);
        break;
      case 3: // POP
        if (!sp) return end(2);
        sp--;
        break;
      case 4: // DUP
        if (!sp) return end(2);
        if (sp > 255) return end(3);
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 5: { // SWAP
        if (sp < 2) return end(2);
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 6: // OVER
        if (sp < 2) return end(2);
        if (sp > 255) return end(3);
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 7: { // ROT (a b c -- b c a)
        if (sp < 3) return end(2);
        const t = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = t;
        break;
      }
      case 0x17: // NEG
        if (!sp) return end(2);
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 0x1b: // NOT
        if (!sp) return end(2);
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: { // binary ops (a b -- r)
        if (sp < 2) return end(2);
        const y = D[sp - 1], x = D[sp - 2];
        let r;
        if (b === 0x10) r = (x + y) | 0;
        else if (b === 0x11) r = (x - y) | 0;
        else if (b === 0x12) r = Math.imul(x, y);
        else if (b === 0x13) {
          if (!y) return end(4);
          r = x === -2147483648 && y === -1 ? x : (x / y) | 0;
        } else if (b === 0x14) {
          if (!y) return end(4);
          r = y === -1 ? 0 : (x % y) | 0;
        } else if (b === 0x15) {
          if (!y) return end(4);
          r = Math.floor((x >>> 0) / (y >>> 0)) | 0;
        } else if (b === 0x16) {
          if (!y) return end(4);
          r = ((x >>> 0) % (y >>> 0)) | 0;
        } else if (b === 0x18) r = x & y;
        else if (b === 0x19) r = x | y;
        else if (b === 0x1a) r = x ^ y;
        else if (b === 0x1c) r = x << (y & 31);
        else if (b === 0x1d) r = x >> (y & 31);
        else if (b === 0x1e) r = (x >>> (y & 31)) | 0;
        else if (b === 0x20) r = x === y ? 1 : 0;
        else if (b === 0x21) r = x < y ? 1 : 0;
        else r = (x >>> 0) < (y >>> 0) ? 1 : 0;
        D[sp - 2] = r;
        sp--;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ
        const rel = ((p[pc - 2] | (p[pc - 1] << 8)) << 16) >> 16;
        if (b === 0x30) { pc += rel; break; }
        if (!sp) return end(2);
        const v = D[--sp];
        if ((b === 0x31) === (v === 0)) pc += rel;
        break;
      }
      case 0x33: // CALL
        if (cp === 64) return end(7);
        C[cp++] = pc;
        pc = p[pc - 2] | (p[pc - 1] << 8);
        break;
      case 0x34: // RET
        if (!cp) return end(8);
        pc = C[--cp];
        break;
      case 0x40: { // LOAD
        if (!sp) return end(2);
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: { // STORE (v addr --)
        if (sp < 2) return end(2);
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        M[a] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no newline
        if (!sp) return end(2);
        const t = String(D[sp - 1]);
        if (ol + t.length > OUT_MAX) return end(11);
        for (let i = 0; i < t.length; i++) o[ol++] = t.charCodeAt(i);
        sp--;
        break;
      }
      case 0x51: // PUTC
        if (!sp) return end(2);
        if (ol >= OUT_MAX) return end(11);
        o[ol++] = D[--sp] & 255;
        break;
      case 0x52: // IN
        if (sp > 255) return end(3);
        D[sp++] = ip < g.length ? g[ip++] : -1;
        break;
      case 0x53: // EXIT
        if (!sp) return end(2);
        return end(D[--sp] & 255);
    }
  }
}

for (const id of readdirSync("/input").sort()) {
  const dir = "/input/" + id;
  const r = run(readFileSync(dir + "/program.bin"), readFileSync(dir + "/input.bin"));
  mkdirSync("/output/" + id, { recursive: true });
  writeFileSync("/output/" + id + "/stdout.bin", r.o);
  writeFileSync("/output/" + id + "/exit.txt", String(r.e) + "\n");
}
