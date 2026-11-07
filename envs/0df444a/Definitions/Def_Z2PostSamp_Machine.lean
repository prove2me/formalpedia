-- Prove2me | Definitions.Def_Z2PostSamp_Machine
-- name    : Z2PostSamp_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:04.20659+00:00
-- url     : https://prove2.me/theorems/2e96e76a-f29c-4714-8e46-9620242262ba
-- title:
--   The randomized log-cost RAM with a clamped dyadic real oracle
-- statement:
--   The model of computation in which "there is a randomized algorithm" is read. A **program** is a finite list of instructions, the same for every input. The machine has a natural-number memory $\mathrm{mem}:\mathbb N\to\mathbb N$ (unwritten cells hold $0$), a program counter, a fair-coin tape $\omega\in\{0,1\}^{\mathbb N}$ and a real **oracle sequence** $x:\mathbb N\to\mathbb R$. Its instructions are:
--
--   1. literals, copies, $+$, truncated $-$, $\times$, integer division and remainder, bitwise xor and and, shifts, indirect load and store, and the jumps on $=$ and $\le$;
--   2. `coin`, which writes the next fair coin;
--   3. `approx d a b`, which writes, for $i=\mathrm{mem}[a]$ and $p=\mathrm{mem}[b]$, the integer $\big\lfloor 2^p\cdot\max(-2^p,\min(2^p,x_i))\big\rfloor$, encoded as a natural number by the zigzag map $z\mapsto 2z$ $(z\ge0)$, $z\mapsto-2z-1$ $(z<0)$;
--   4. `halt s ℓ`, which outputs $\mathrm{mem}[s],\dots,\mathrm{mem}[s+\ell-1]$.
--
--   Every instruction is charged $1$ plus the bit lengths of the addresses, operands and results it touches; `approx` is charged in addition $p$, the number of requested bits. A halted machine stutters at zero cost, and a program counter outside the program is stuck and keeps being charged. `HaltsWithin` says that the machine halts with log-cost at most a bound $B$; `coinLaw` is the law of i.i.d. fair coins.
--
--   This is the paper's computational convention: the real observation and the known parameter are accessed only through deterministic dyadic approximations, and the cost includes all requested bits and the subsequent bit operations.
--
--   **Formalization Note** The paper names no machine. The instruction set and charging follow the published `AlgoPFR.Machine`; its sample and query oracles are replaced by the single dyadic real oracle. The clamp at $\pm2^p$ means a request for precision $p$ returns $p$ integer and $p$ fractional bits, so a cost bound can hold for every real input; a unit-cost real RAM would not be the paper's bit-cost convention.
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), §2 preamble, p.6 (computational convention); App. B.5, p.41 (fair-bit draws)

import Mathlib

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace Z2PostSamp

noncomputable section

/-!
# The randomized log-cost RAM with a dyadic real oracle

Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), §2 preamble, p.6: "We access the real observation and known parameter through
deterministic dyadic approximations. Computational cost includes all requested bits and subsequent
bit operations." App. B.5, p.41: every random draw is made from fair bits.

**Formalization Note.** The paper names no machine. This is a log-cost RAM with natural-number
memory, patterned on the published `AlgoPFR.Machine` (same arithmetic, bitwise, load, store and jump
instructions and the same charging: one plus the bit lengths of every address, operand and result).
Its two oracles are replaced by one real oracle `x : ℕ → ℝ`, read only through the instruction
`approx d a b`, which writes the dyadic approximation `⌊2^p · clamp(x_i, −2^p, 2^p)⌋` (`i = mem[a]`,
`p = mem[b]`), encoded as a natural number by the zigzag map, and is charged its address and operand
bits, the answer's bits, **and `p`** (the requested bits, in unary). Clamping at `±2^p` makes a
request for precision `p` return `p` integer and `p` fractional bits, so a cost bound can hold for
every real input. Randomness is a tape of fair coins read by `coin`. A unit-cost real RAM is not
used: the paper's convention is bit cost.
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
  /-- `mem[d] :=` bitwise xor of `mem[a]`, `mem[b]`. -/
  | xor (d a b : ℕ)
  /-- `mem[d] :=` bitwise and of `mem[a]`, `mem[b]`. -/
  | land (d a b : ℕ)
  /-- `mem[d] := mem[a] * 2 ^ mem[b]`. -/
  | shl (d a b : ℕ)
  /-- `mem[d] := mem[a] / 2 ^ mem[b]`. -/
  | shr (d a b : ℕ)
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
  /-- `mem[d] :=` the zigzag code of `⌊2^p · clamp(x_i, −2^p, 2^p)⌋` with `i = mem[a]`, `p = mem[b]`. -/
  | approx (d a b : ℕ)
  /-- Halt with output `mem[s], …, mem[s + ℓ - 1]`. -/
  | halt (s ℓ : ℕ)

/-- A program is a finite list of instructions, the same for every input. -/
abbrev Program := List Instr

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

/-- The zigzag code of an integer: `z ↦ 2z` for `z ≥ 0`, `z ↦ −2z − 1` for `z < 0`. -/
def zig (z : ℤ) : ℕ := if 0 ≤ z then 2 * z.toNat else 2 * (-z).toNat - 1

/-- The oracle answer to a request for entry `i` at precision `p`:
`⌊2^p · max(−2^p, min(2^p, x_i))⌋`, zigzag-encoded. -/
def approxAnswer (x : ℕ → ℝ) (i p : ℕ) : ℕ :=
  zig ⌊(2 : ℝ) ^ p * max (-(2 : ℝ) ^ p) (min ((2 : ℝ) ^ p) (x i))⌋

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

open Classical in
/-- One instruction, with oracle sequence `x` and coin tape `ω`. -/
def exec (x : ℕ → ℝ) (ω : ℕ → Bool) (i : Instr) (s : MState) : MState :=
  match i with
  | .lit d v => s.write d v (1 + bits d + bits v)
  | .copy d a => s.write d (s.mem a) (1 + bits d + bits a + bits (s.mem a))
  | .add d a b => s.binop (· + ·) d a b
  | .sub d a b => s.binop (· - ·) d a b
  | .mul d a b => s.binop (· * ·) d a b
  | .div d a b => s.binop (· / ·) d a b
  | .mod d a b => s.binop (· % ·) d a b
  | .xor d a b => s.binop Nat.xor d a b
  | .land d a b => s.binop Nat.land d a b
  | .shl d a b => s.binop Nat.shiftLeft d a b
  | .shr d a b => s.binop Nat.shiftRight d a b
  | .load d a =>
    s.write d (s.mem (s.mem a))
      (1 + bits d + bits a + bits (s.mem a) + bits (s.mem (s.mem a)))
  | .store a b =>
    s.write (s.mem a) (s.mem b) (1 + bits a + bits b + bits (s.mem a) + bits (s.mem b))
  | .jeq a b t => s.branch (s.mem a = s.mem b) a b t
  | .jle a b t => s.branch (s.mem a ≤ s.mem b) a b t
  | .coin d =>
    { s.write d (if ω s.coins then 1 else 0) (2 + bits d) with coins := s.coins + 1 }
  | .approx d a b =>
    let v := approxAnswer x (s.mem a) (s.mem b)
    s.write d v (1 + bits d + bits a + bits b + bits (s.mem a) + bits (s.mem b) + s.mem b + bits v)
  | .halt a ℓ =>
    let o := (List.range ℓ).map fun i => s.mem (a + i)
    { s with
      out := some o
      cost := s.cost + (1 + bits a + bits ℓ + (o.map bits).sum) }

/-- One machine step. A halted machine stutters at zero cost; a program counter outside the program
is stuck and keeps being charged, so a program cannot halt by running off its end. -/
def step (P : Program) (x : ℕ → ℝ) (ω : ℕ → Bool) (s : MState) : MState :=
  match s.out with
  | some _ => s
  | none =>
    match P[s.pc]? with
    | none => { s with cost := s.cost + 1 }
    | some i => exec x ω i s

/-- The state after `t` steps on the given input. -/
def run (P : Program) (x : ℕ → ℝ) (input : List ℕ) (ω : ℕ → Bool) (t : ℕ) : MState :=
  (step P x ω)^[t] (initState input)

/-- On the tape `ω` the machine halts, and its log-cost time at the halting step is at most `B`. -/
def HaltsWithin (P : Program) (x : ℕ → ℝ) (input : List ℕ) (ω : ℕ → Bool) (B : ℕ) : Prop :=
  ∃ t, (run P x input ω t).out.isSome ∧ (run P x input ω t).cost ≤ B

/-- The output after `T` steps (`none` if the machine has not halted). -/
def outputAt (P : Program) (x : ℕ → ℝ) (input : List ℕ) (ω : ℕ → Bool) (T : ℕ) :
    Option (List ℕ) :=
  (run P x input ω T).out

/-- The law of the coin tape: independent fair coins. -/
def coinLaw : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

end

end Z2PostSamp


