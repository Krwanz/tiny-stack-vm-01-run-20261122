// Tiny stack VM: a correct interpreter for make.fun's tiny stack ISA v1.
// One run answers every instance in /input/<id>/, writing /output/<id>/stdout.bin
// and /output/<id>/exit.txt. Node 22, built-ins only, fully deterministic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per opcode byte: immediate length, values popped, values pushed, packed as
// imm | pops << 8 | pushes << 16. -1 marks a byte no opcode names (trap 5).
const TAB = new Int32Array(256).fill(-1);
for (const [op, im, po, pu] of [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0],
  [0x04, 0, 1, 2], [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3],
  [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1], [0x13, 0, 2, 1],
  [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1], [0x17, 0, 1, 1],
  [0x18, 0, 2, 1], [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1], [0x20, 0, 2, 1],
  [0x21, 0, 2, 1], [0x22, 0, 2, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0],
  [0x32, 2, 1, 0], [0x33, 2, 0, 0], [0x34, 0, 0, 0], [0x40, 0, 1, 1],
  [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1],
  [0x53, 0, 1, 0],
]) TAB[op] = im | (po << 8) | (pu << 16);

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const S = new Int32Array(256); // data stack, at most 256 values
  const C = new Int32Array(64); // call stack, at most 64 return addresses
  const M = new Int32Array(256); // memory, 256 words, all zero at the start
  const out = new Uint8Array(65536);
  const tmp = new Uint8Array(12); // scratch for one PRINT's decimal digits
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, steps = 0;
  const end = (code: number) => ({ out: out.subarray(0, ol), code });
  for (;;) {
    // Step order: step limit, pc range, opcode, immediate, then the step
    // counts and the stack needs are checked, then the instruction runs.
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    const e = TAB[op];
    if (e < 0) return end(5);
    const im = e & 255;
    if (pc + im >= n) return end(9);
    steps++;
    const pops = (e >> 8) & 255, pushes = (e >> 16) & 255;
    if (sp < pops) return end(2);
    if (sp - pops + pushes > 256) return end(3);
    const nx = pc + 1 + im;
    pc = nx;
    switch (op) {
      case 0x00: return end(0);
      case 0x01: S[sp++] = (p[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: S[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: S[sp] = S[sp - 1]; sp++; break;
      case 0x05: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; }
      case 0x06: S[sp] = S[sp - 2]; sp++; break;
      case 0x07: { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; break; }
      case 0x17: S[sp - 1] = -S[sp - 1] | 0; break; // NEG, wraps at -2147483648
      case 0x1b: S[sp - 1] = ~S[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = S[sp - 1], a = S[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b); // low 32 bits of the exact product
        else if (op === 0x13) { // DIV, truncated toward zero
          if (b === 0) return end(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) { // MOD, sign of a
          if (b === 0) return end(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) { // DIVU, unsigned
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) { // MODU, unsigned
          if (b === 0) return end(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31); // only the low 5 bits count
        else if (op === 0x1d) r = a >> (b & 31); // arithmetic
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0; // logical
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0; // signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // unsigned
        sp -= 2;
        S[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ; offset signed, relative to nx
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        if (op === 0x30) pc = nx + rel;
        else { const v = S[--sp]; if ((op === 0x31) === (v === 0)) pc = nx + rel; }
        break;
      }
      case 0x33: // CALL; target unsigned, return address is nx
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 0x40: { // LOAD
        const a = S[sp - 1];
        if (a < 0 || a >= 256) return end(6);
        S[sp - 1] = M[a];
        break;
      }
      case 0x41: { // STORE; the top is the address, below it the value
        const a = S[sp - 1];
        if (a < 0 || a >= 256) return end(6);
        M[a] = S[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT, decimal ASCII; trap 11 writes none of it
        const v = S[sp - 1];
        let u = v < 0 ? -v : v; // -(-2147483648) is 2147483648, exact as a double
        let k = 0;
        do { tmp[k++] = 48 + (u % 10); u = Math.floor(u / 10); } while (u > 0);
        if (v < 0) tmp[k++] = 45;
        if (ol + k > 65536) return end(11);
        sp--;
        for (let i = k - 1; i >= 0; i--) out[ol++] = tmp[i];
        break;
      }
      case 0x51: // PUTC, one byte
        if (ol + 1 > 65536) return end(11);
        out[ol++] = S[--sp] & 255;
        break;
      case 0x52: S[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN, -1 past the end
      case 0x53: return end(S[--sp] & 255); // EXIT, low byte of the code
      default: return end(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
