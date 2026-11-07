-- Prove2me | Definitions.Def_IterRoundDet_Machine
-- name    : IterRoundDet_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:45.64261+00:00
-- url     : https://prove2.me/theorems/99131a9d-0b9f-4b12-88f0-e75d63f8d317
-- title:
--   A log-cost oracle RAM with coins
-- statement:
--   The paper says "polynomial-time algorithm" and counts bits ("maximum bit length", p.19; "Controlling bit lengths", p.21; "polynomial oracle and bit complexity", p.41), but names no machine. This file fixes one.
--
--   A program is a finite list of instructions over a memory of natural numbers. The instructions are literals, copies, the five arithmetic operations, indirect load and store, two conditional jumps, a fair coin, an oracle query, and halt. Each step costs one plus the bit lengths of its addresses, operands and result. A query sends a list of cells and is charged the length of the list and the bits of the list and of the answer.
--
--   A program is deterministic if it contains no coin. A finite coin string extends to a tape by `false`; a run of $T$ steps reads at most $T$ coins.
--
--   **Formalization Note** Memory addresses and lengths of `query` and `halt` are read from registers, as a fixed program must handle every $n$. A halted machine stutters at no cost, and a program counter outside the program is stuck and charged, so only `halt` halts.
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Theorem 1.1, p.2; §4, p.19; Lemma C.1, Lemma D.2

import Mathlib

set_option autoImplicit false

namespace IterRoundDet

/-!
# The log-cost oracle RAM

Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…). Theorem 1.1, p.2, says "there
is a polynomial-time algorithm"; §4 counts bits: "maximum bit length" (p.19), "Controlling bit lengths"
(p.21), "polynomial oracle and bit complexity" (Lemma D.2, p.41).

**Formalization Note.** The paper names no machine. This is a log-cost RAM with natural-number memory:
a program is a finite list of instructions, no instruction carries a function, and a step costs `1`
plus the bit lengths of every address, operand and result. The one non-arithmetic instruction besides
`coin` is `query`, which sends a list of cells to an oracle. The memory addresses and lengths of `query`
and `halt` are read from registers, since a fixed program must handle every `n`. Both are charged the
length in unary as well as the bit length of every cell read or written, so a long list of zeros is not
free. Oracle answers are charged: a long answer costs its length.
-/

/-- The instruction set. Operands are memory addresses; `lit` writes a literal. -/
inductive Instr
  /-- `mem[d] := v`. -/
  | lit (d v : ℕ)
  /-- `mem[d] := mem[s]`. -/
  | copy (d s : ℕ)
  /-- `mem[d] := mem[a] + mem[b]`. -/
  | add (d a b : ℕ)
  /-- `mem[d] := mem[a] - mem[b]`, truncated at `0`. -/
  | sub (d a b : ℕ)
  /-- `mem[d] := mem[a] * mem[b]`. -/
  | mul (d a b : ℕ)
  /-- `mem[d] := mem[a] / mem[b]`, with `x / 0 = 0`. -/
  | div (d a b : ℕ)
  /-- `mem[d] := mem[a] % mem[b]`. -/
  | mod (d a b : ℕ)
  /-- `mem[d] := mem[mem[a]]`. -/
  | load (d a : ℕ)
  /-- `mem[mem[a]] := mem[s]`. -/
  | store (a s : ℕ)
  /-- Jump to `t` if `mem[a] = mem[b]`. -/
  | jeq (a b t : ℕ)
  /-- Jump to `t` if `mem[a] ≤ mem[b]`. -/
  | jle (a b t : ℕ)
  /-- `mem[d] :=` the next fair coin, `0` or `1`. -/
  | coin (d : ℕ)
  /-- Send `mem[mem[s]], …, mem[mem[s] + mem[l] - 1]` to oracle `tag`, and write the answer from cell
  `mem[d]` on. -/
  | query (tag d s l : ℕ)
  /-- Halt with output `mem[mem[s]], …, mem[mem[s] + mem[l] - 1]`. -/
  | halt (s l : ℕ)

/-- A program is a finite list of instructions, the same for every input. -/
abbrev Program := List Instr

/-- `P` uses no coin: the algorithm is deterministic. -/
def CoinFree (P : Program) : Prop := ∀ i ∈ P, ∀ d, i ≠ Instr.coin d

/-- An oracle answers a list of natural numbers, sent under a tag, with a list of natural numbers. -/
abbrev Oracle := ℕ → List ℕ → List ℕ

/-- A machine state. -/
structure MState where
  /-- The program counter. -/
  pc : ℕ
  /-- The memory; unwritten cells hold `0`. -/
  mem : ℕ → ℕ
  /-- The number of fair coins read so far. -/
  coins : ℕ
  /-- The log-cost time charged so far. -/
  cost : ℕ
  /-- The output, once the machine has halted. -/
  out : Option (List ℕ)

/-- The input convention: the list of naturals in cells `0, 1, …`, everything else `0`. -/
def initState (input : List ℕ) : MState :=
  ⟨0, fun i => input.getD i 0, 0, 0, none⟩

/-- The bit length of a natural number, `Nat.size 0 = 0`. -/
abbrev bits (x : ℕ) : ℕ := Nat.size x

/-- The cells `mem[s], …, mem[s + l - 1]`. -/
def readCells (mem : ℕ → ℕ) (s l : ℕ) : List ℕ := (List.range l).map fun k => mem (s + k)

/-- The memory with the list `ans` written from cell `d` on. -/
def writeCells (mem : ℕ → ℕ) (d : ℕ) (ans : List ℕ) : ℕ → ℕ :=
  fun k => if d ≤ k ∧ k < d + ans.length then ans.getD (k - d) 0 else mem k

/-- The total bit length of a list. -/
def listBits (l : List ℕ) : ℕ := (l.map bits).sum

/-- Writes `v` into cell `d`, advances the program counter and charges `c`. -/
def MState.write (s : MState) (d v c : ℕ) : MState :=
  { s with pc := s.pc + 1, mem := Function.update s.mem d v, cost := s.cost + c }

/-- The charged binary operation `mem[d] := g mem[a] mem[b]`. -/
def MState.binop (s : MState) (g : ℕ → ℕ → ℕ) (d a b : ℕ) : MState :=
  let v := g (s.mem a) (s.mem b)
  s.write d v (1 + bits d + bits a + bits b + bits (s.mem a) + bits (s.mem b) + bits v)

/-- The charged conditional jump. -/
def MState.branch (s : MState) (c : Prop) [Decidable c] (a b t : ℕ) : MState :=
  { s with
    pc := if c then t else s.pc + 1
    cost := s.cost + (1 + bits a + bits b + bits t + bits (s.mem a) + bits (s.mem b)) }

/-- One instruction, with oracle `O` and coin tape `ω`. -/
def exec (O : Oracle) (ω : ℕ → Bool) (i : Instr) (s : MState) : MState :=
  match i with
  | .lit d v => s.write d v (1 + bits d + bits v)
  | .copy d a => s.write d (s.mem a) (1 + bits d + bits a + bits (s.mem a))
  | .add d a b => s.binop (· + ·) d a b
  | .sub d a b => s.binop (· - ·) d a b
  | .mul d a b => s.binop (· * ·) d a b
  | .div d a b => s.binop (· / ·) d a b
  | .mod d a b => s.binop (· % ·) d a b
  | .load d a =>
    s.write d (s.mem (s.mem a))
      (1 + bits d + bits a + bits (s.mem a) + bits (s.mem (s.mem a)))
  | .store a b =>
    s.write (s.mem a) (s.mem b) (1 + bits a + bits b + bits (s.mem a) + bits (s.mem b))
  | .jeq a b t => s.branch (s.mem a = s.mem b) a b t
  | .jle a b t => s.branch (s.mem a ≤ s.mem b) a b t
  | .coin d =>
    { s.write d (if ω s.coins then 1 else 0) (2 + bits d) with coins := s.coins + 1 }
  | .query tag d a l =>
    let q := readCells s.mem (s.mem a) (s.mem l)
    let ans := O tag q
    { s with
      pc := s.pc + 1
      mem := writeCells s.mem (s.mem d) ans
      cost := s.cost + (1 + bits tag + bits d + bits a + bits l + bits (s.mem d) + bits (s.mem a) +
        bits (s.mem l) + q.length + listBits q + ans.length + listBits ans) }
  | .halt a l =>
    let o := readCells s.mem (s.mem a) (s.mem l)
    { s with
      out := some o
      cost := s.cost + (1 + bits a + bits l + bits (s.mem a) + bits (s.mem l) + o.length +
        listBits o) }

/-- One machine step. A halted machine stutters at zero cost; a program counter outside the program
is stuck and keeps being charged, so a program cannot halt by running off its end. Every step before
halting costs at least `1`, so the cost is at least the number of steps taken. -/
def step (P : Program) (O : Oracle) (ω : ℕ → Bool) (s : MState) : MState :=
  match s.out with
  | some _ => s
  | none =>
    match P[s.pc]? with
    | none => { s with cost := s.cost + 1 }
    | some i => exec O ω i s

/-- The state after `t` steps on the given input. -/
def run (P : Program) (O : Oracle) (input : List ℕ) (ω : ℕ → Bool) (t : ℕ) : MState :=
  (step P O ω)^[t] (initState input)

/-- A finite coin string as a tape, `false` beyond its end. A run of `T` steps reads at most `T`
coins, so `Fin T → Bool` carries everything such a run can see. -/
def extendBits {T : ℕ} (w : Fin T → Bool) : ℕ → Bool :=
  fun k => if h : k < T then w ⟨k, h⟩ else false

end IterRoundDet


