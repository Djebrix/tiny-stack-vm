// tiny-stack-vm: a compact interpreter for make.fun's tiny stack ISA (ISA.md).
// One run answers all 40 instances in /input: for each, run its program.bin
// on input.bin and write /output/<id>/stdout.bin + exit.txt. Deterministic:
// no clock, no env, no reads outside /input and /bot.
//
// Check order per step follows the reference VM exactly: step limit (10),
// pc outside program (9), unknown opcode (5), truncated immediate (9),
// stack underflow (2), stack overflow (3), then the instruction's own traps
// (div by zero 4, memory 6, call depth 7, empty RET 8, output limit 11).
// A trap keeps the output written before it.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode table: bit 7 = defined, bits 6-4 = immediate bytes, bits 3-2 = pops, bits 1-0 = pushes.
const T = new Uint8Array(256);
for (const [o, i, p, u] of [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2],
  [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3], [48, 2, 0, 0], [49, 2, 1, 0],
  [50, 2, 1, 0], [51, 2, 0, 0], [52, 0, 0, 0], [64, 0, 1, 1], [65, 0, 2, 0],
  [80, 0, 1, 0], [81, 0, 1, 0], [82, 0, 0, 1], [83, 0, 1, 0],
]) T[o] = 128 | (i << 4) | (p << 2) | u;
for (let o = 16; o <= 34; o++) if (o !== 23 && o !== 27) T[o] = 137; // binary ops: pop 2, push 1
T[23] = 133; // NEG: pop 1, push 1
T[27] = 133; // NOT: pop 1, push 1

function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, pc = 0, steps = 0, ip = 0, ol = 0;
  const done = (code) => [out.subarray(0, ol), code];
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc];
    const t = T[op];
    if (!t) return done(5);
    const imm = (t >> 4) & 7, pops = (t >> 2) & 3, push = t & 3;
    if (pc + imm >= n) return done(9);
    steps++;
    if (sp < pops) return done(2);
    if (sp - pops + push > 256) return done(3);
    const nx = pc + 1 + imm;
    pc = nx;
    switch (op) {
      case 0: return done(0); // HALT
      case 1: D[sp++] = (p[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break; // PUSH32
      case 3: sp--; break; // POP
      case 4: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 5: { const x = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = x; break; } // SWAP
      case 6: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 23: D[sp - 1] = (-D[sp - 1]) | 0; break; // NEG (wraps: -INT_MIN stays INT_MIN)
      case 27: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 48: case 49: case 50: { // JMP / JZ / JNZ
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = op === 48;
        if (op !== 48) { const v = D[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 51: // CALL
        if (csp === 64) return done(7);
        C[csp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52: // RET
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 64: { // LOAD
        const a = D[sp - 1];
        if (a < 0 || a > 255) return done(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: { // STORE (top of stack is the address)
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a > 255) return done(6);
        sp -= 2;
        M[a] = v;
        break;
      }
      case 80: { // PRINT: decimal ASCII, no newline
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 81: // PUTC
        if (ol + 1 > 65536) return done(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN (-1 when exhausted)
      case 83: return done(D[--sp] & 255); // EXIT: low byte
      default: { // binary ops 0x10-0x22 except NEG/NOT
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        switch (op) {
          case 16: r = (a + b) | 0; break; // ADD wraps
          case 17: r = (a - b) | 0; break; // SUB wraps
          case 18: r = Math.imul(a, b); break; // MUL low 32 bits, exact
          case 19: // DIV, truncated toward zero; INT_MIN / -1 wraps to INT_MIN
            if (b === 0) return done(4);
            r = (a / b) | 0;
            break;
          case 20: // MOD, sign of the dividend; x % -1 is 0
            if (b === 0) return done(4);
            r = (a % b) | 0;
            break;
          case 21: // DIVU, unsigned
            if (b === 0) return done(4);
            r = ((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 22: // MODU, unsigned
            if (b === 0) return done(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 24: r = a & b; break;
          case 25: r = a | b; break;
          case 26: r = a ^ b; break;
          case 28: r = a << b; break; // shift count: low 5 bits (JS masks already)
          case 29: r = a >> b; break; // arithmetic
          case 30: r = (a >>> b) | 0; break; // logical, read back signed
          case 32: r = a === b ? 1 : 0; break; // EQ
          case 33: r = a < b ? 1 : 0; break; // LT signed
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU unsigned
        }
        sp -= 2;
        D[sp++] = r;
      }
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const [o, c] = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), o);
  writeFileSync(join(O, id, 'exit.txt'), c + '\n');
}
