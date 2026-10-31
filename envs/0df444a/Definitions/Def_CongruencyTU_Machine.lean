-- Prove2me | Definitions.Def_CongruencyTU_Machine
-- name    : CongruencyTU_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:02.340735+00:00
-- url     : https://prove2.me/theorems/3b0b1142-c1cb-45f1-aa0c-a4fb31530188
-- title:
--   Integer RAM with unit-cost arithmetic, coins and an oracle; strongly polynomial and randomized algorithms
-- statement:
--   The paper states its algorithmic results ("strongly polynomial-time", "randomized") without fixing a machine. This definition fixes one, shared by every algorithmic statement of the mission.
--
--   A **program** is a finite list of instructions over integer registers $R[0], R[1], \dots$: load a constant, copy, $+$, $-$, $\times$, integer division and remainder (Euclidean, $x \bmod 0 = x$, $x \,\mathrm{div}\, 0 = 0$), branch on $\le$, indirect load $R[d] := R[R[a]]$ and store $R[R[a]] := R[s]$, *coin* (read the next random bit), *query* (send a block of registers to an oracle and receive its answer), and halt. Every instruction costs one unit; a query costs $1$ plus the lengths of the question and the answer.
--
--   An input is a list $I$ of integers; its **dimension** is its length and its **bit size** is $\sigma(I)=\sum_{z\in I}(1+\lceil\log_2(|z|+1)\rceil)$. The output is the list $R[1],\dots,R[R[0]]$ when the machine halts.
--
--   1. A **deterministic strongly polynomial algorithm** for a relation is one program with polynomials $p, q$, fixed before the input, such that on every admissible input the run halts with cost at most $p(\text{dimension})$, every register at every step has bit length at most $q(\sigma)$, and the output is correct.
--   2. A **randomized strongly polynomial algorithm** (footnote 4 of the paper) uses $N = p(\text{dimension})$ uniformly random coins: every run is bounded as above, on an infeasible instance every coin string yields the answer "infeasible", and on a feasible instance at least a $1-1/n$ fraction of coin strings yields a correct answer, $n$ the number of variables.
--
--   The bit-length clause prevents unit-cost multiplication from manipulating exponentially long numbers. Integer remainder is a unit operation because without it Theorem 1 is false: for the fixed-dimension instance $0\le x_1\le 1$, $x_2=0$, $\gamma_1x_1\equiv 1 \pmod 3$, feasibility is $\gamma_1\equiv 1\pmod 3$, which no bounded number of $+,-,\times,/,\le$ operations decides for all $\gamma_1$.
--
--   **Formalization Note** Programs are `List Instr`; `run P O c I t` is the state after $t$ steps with oracle `O` and coin string `c`; `RunBounded`, `DetSolves`, `RandSolves`, `DetRunOK`, `detOut`, `queryAt` and `pack` (framing a list of lists) are the predicates and helpers used by the theorems. Probabilities are counts over `Fin N → Bool` in $\mathbb Q$.
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, §1.1, Theorem 1 and footnote 4, p.2 (PDF p.3): "strongly polynomial-time randomized algorithm"; the model is the standard one for integer input (paper.md R1, R2)

import Mathlib

open Classical

namespace CongruencyTU

/-! # The cost model: an integer RAM with unit-cost arithmetic, coins and an oracle

Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*,
arXiv:2109.03148v3 (preprint). The paper uses "strongly polynomial(-time)" (Theorem 1, p.2, and
throughout) without defining it, and calls an algorithm *randomized* in the sense of footnote 4, p.2:
"one that always correctly detects infeasibility of a problem, and finds a solution of a feasible
problem with high probability 1 − 1/n, where n is the number of variables."

This module fixes one machine model, shared by every algorithmic statement of the mission.

**Formalization Note.**
* A *program* is a finite list of instructions, fixed before the input. Registers are indexed by `ℕ`
  and hold integers; all registers start at `0` except the input block.
* Unit-cost instructions: load constant, copy, `+`, `−`, `×`, `Int.ediv`, `Int.emod` (Lean's
  conventions: `x / 0 = 0`, `x % 0 = x`), branch on `≤`, indirect load `R[d] := R[R[a]]` and store
  `R[R[a]] := R[s]` (a negative address is read as `0`, `Int.toNat`), `coin d` (writes the next bit of
  the coin string, `1` or `0`, into `R[d]`), and `query a`. Integer remainder is a unit operation on
  purpose: with only `+, −, ×, /` and comparisons, Theorem 1 is false (an instance of fixed dimension
  whose feasibility is `γ₁ ≡ 1 (mod 3)` cannot be decided with a bounded number of such operations).
* `query a` sends the block `R[a+1], …, R[a+ℓ]` with `ℓ = R[a]` to the oracle and overwrites the block
  starting at `a` with the answer (its length into `R[a]`). It costs `1 + ℓ + |answer|`. Programs used
  without an oracle are run with `noOracle`.
* *Input*: a list `I` of integers, stored as `R[0] = |I|`, `R[i+1] = I[i]`. *Dimension* is `|I|`;
  *bit size* `σ(I) = Σ (1 + Nat.size |z|)`.
* *Output*: when the machine halts (program counter on `halt` or outside the program), the list
  `R[1], …, R[R[0]]`.
* *Strongly polynomial*: the total cost up to halting is at most `p(dimension)` and every register at
  every step has bit length at most `q(σ(I) + extra + bits of the oracle answers received so far)`,
  for polynomials `p q : ℕ[X]` fixed before the input. The bit-length clause is what keeps unit-cost
  multiplication honest.
* *Coins*: a coin string is `Fin N → Bool` with `N = p(dimension)`, uniformly distributed; a run of
  cost at most `N` reads at most `N` coins. Probabilities are counts over this finite set, in `ℚ`. -/

/-- Instructions of the integer RAM (see the module docstring). -/
inductive Instr where
  | const (d : ℕ) (c : ℤ)
  | copy (d s : ℕ)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | mul (d a b : ℕ)
  | div (d a b : ℕ)
  | mod (d a b : ℕ)
  | jle (a b target : ℕ)
  | load (d a : ℕ)
  | store (a s : ℕ)
  | coin (d : ℕ)
  | query (a : ℕ)
  | halt
  deriving DecidableEq

/-- A program: a finite list of instructions, fixed independently of the input. -/
abbrev Program := List Instr

/-- An oracle answers a list of integers with a list of integers. -/
abbrev Oracle := List ℤ → List ℤ

/-- The trivial oracle, for programs that make no queries. -/
def noOracle : Oracle := fun _ => []

/-- Bit size `σ(I) = Σ_{z ∈ I} (1 + Nat.size |z|)` of a list of integers. -/
def bitSize (I : List ℤ) : ℕ := (I.map fun z => 1 + Nat.size z.natAbs).sum

/-- Machine state: program counter, registers, number of coins read, accumulated cost, number of
oracle queries made, and total bit size of the oracle answers received. -/
structure State where
  pc : ℕ
  reg : ℕ → ℤ
  coinsRead : ℕ
  cost : ℕ
  queries : ℕ
  ansBits : ℕ

/-- The block `R[a+1], …, R[a+len]`. -/
def readBlock (reg : ℕ → ℤ) (a len : ℕ) : List ℤ :=
  (List.range len).map fun i => reg (a + 1 + i)

/-- Write the list `l` as a block at `a`: `R[a] := |l|`, `R[a+1+i] := l[i]`. -/
def writeBlock (reg : ℕ → ℤ) (a : ℕ) (l : List ℤ) : ℕ → ℤ := fun j =>
  if j = a then (l.length : ℤ)
  else if a + 1 ≤ j ∧ j < a + 1 + l.length then l.getD (j - (a + 1)) 0
  else reg j

/-- Initial state on input `I`. -/
def initState (I : List ℤ) : State where
  pc := 0
  reg := fun j => if j = 0 then (I.length : ℤ) else I.getD (j - 1) 0
  coinsRead := 0
  cost := 0
  queries := 0
  ansBits := 0

/-- The machine has halted: the program counter is on `halt` or outside the program. -/
def isHalted (P : Program) (s : State) : Bool :=
  match P[s.pc]? with
  | none => true
  | some .halt => true
  | some _ => false

/-- Write `v` into register `d`, advance the program counter, pay one unit. -/
def State.setNext (s : State) (d : ℕ) (v : ℤ) : State :=
  { s with reg := Function.update s.reg d v, pc := s.pc + 1, cost := s.cost + 1 }

/-- One step of the machine with oracle `O` and coin string `c`. A halted state is fixed. -/
def step (P : Program) (O : Oracle) (c : ℕ → Bool) (s : State) : State :=
  match P[s.pc]? with
  | none => s
  | some .halt => s
  | some (.const d v) => s.setNext d v
  | some (.copy d a) => s.setNext d (s.reg a)
  | some (.add d a b) => s.setNext d (s.reg a + s.reg b)
  | some (.sub d a b) => s.setNext d (s.reg a - s.reg b)
  | some (.mul d a b) => s.setNext d (s.reg a * s.reg b)
  | some (.div d a b) => s.setNext d (s.reg a / s.reg b)
  | some (.mod d a b) => s.setNext d (s.reg a % s.reg b)
  | some (.jle a b t) =>
      { s with pc := if s.reg a ≤ s.reg b then t else s.pc + 1, cost := s.cost + 1 }
  | some (.load d a) => s.setNext d (s.reg (s.reg a).toNat)
  | some (.store a v) => s.setNext (s.reg a).toNat (s.reg v)
  | some (.coin d) =>
      { s.setNext d (if c s.coinsRead then 1 else 0) with coinsRead := s.coinsRead + 1 }
  | some (.query a) =>
      let len := (s.reg a).toNat
      let ans := O (readBlock s.reg a len)
      { s with reg := writeBlock s.reg a ans, pc := s.pc + 1,
               cost := s.cost + 1 + len + ans.length, queries := s.queries + 1,
               ansBits := s.ansBits + bitSize ans }

/-- The state after `t` steps on input `I`. -/
def run (P : Program) (O : Oracle) (c : ℕ → Bool) (I : List ℤ) : ℕ → State
  | 0 => initState I
  | t + 1 => step P O c (run P O c I t)

/-- The output list `R[1], …, R[R[0]]` of a state. -/
def outputOf (s : State) : List ℤ := readBlock s.reg 0 (s.reg 0).toNat

/-- A run is **strongly polynomially bounded** by `B` (cost) and `q` (bit length): it halts at some
step with accumulated cost at most `B`, and at every step every register has bit length at most
`q(σ(I) + extra + bits of oracle answers received so far)`. -/
def RunBounded (P : Program) (O : Oracle) (c : ℕ → Bool) (I : List ℤ) (B : ℕ)
    (q : Polynomial ℕ) (extra : ℕ) : Prop :=
  (∃ t, isHalted P (run P O c I t) = true ∧ (run P O c I t).cost ≤ B) ∧
  ∀ t j, Nat.size ((run P O c I t).reg j).natAbs ≤
    q.eval (bitSize I + extra + (run P O c I t).ansBits)

/-- The output after `B` steps (for a run bounded by `B` this is the output at halting, since every
step costs at least one unit and a halted state is fixed). -/
def outputAfter (P : Program) (O : Oracle) (c : ℕ → Bool) (I : List ℤ) (B : ℕ) : List ℤ :=
  outputOf (run P O c I B)

/-- The all-`false` coin string, used for deterministic algorithms. -/
def noCoins : ℕ → Bool := fun _ => false

/-- Extend a finite coin string by `false`. -/
def extendCoins {N : ℕ} (c : Fin N → Bool) : ℕ → Bool :=
  fun i => if h : i < N then c ⟨i, h⟩ else false

/-- **Deterministic strongly polynomial algorithm.** One program `P` and polynomials `p q`, fixed
before the input, such that on every input `a` with `Dom a`, the run on `enc a` without coins and
without oracle has cost at most `p(size a)`, bit lengths bounded by `q(σ(enc a) + size a)`, and an
output satisfying `Good a`. For the standard notion `size a = |enc a|`; a unary encoded objective
adds its sup-norm to `size`. -/
def DetSolves {α : Type*} (enc : α → List ℤ) (size : α → ℕ) (Dom : α → Prop)
    (Good : α → List ℤ → Prop) : Prop :=
  ∃ (P : Program) (p q : Polynomial ℕ), ∀ a, Dom a →
    RunBounded P noOracle noCoins (enc a) (p.eval (size a)) q (size a) ∧
    Good a (outputAfter P noOracle noCoins (enc a) (p.eval (size a)))

/-- **Randomized strongly polynomial algorithm in the sense of footnote 4, p.2.** One program `P`
and polynomials `p q`, fixed before the input, such that on every input `a` with `Dom a`, with
`N = p(size a)` coins:
1. every run (every coin string) is bounded by cost `N` and bit length `q(σ(enc a) + size a)`;
2. if `Feasible a` fails, every coin string yields the output `[0]` ("infeasible");
3. if `Feasible a` holds, the fraction of coin strings whose output satisfies `Good a` is at least
   `1 − 1/nvars a` (computed in `ℚ`; at `nvars a = 0` Lean's `1/0 = 0` makes this `1`). -/
def RandSolves {α : Type*} (enc : α → List ℤ) (size : α → ℕ) (Dom : α → Prop)
    (nvars : α → ℕ) (Feasible : α → Prop) (Good : α → List ℤ → Prop) : Prop :=
  ∃ (P : Program) (p q : Polynomial ℕ), ∀ a, Dom a →
    (∀ c : Fin (p.eval (size a)) → Bool,
      RunBounded P noOracle (extendCoins c) (enc a) (p.eval (size a)) q (size a)) ∧
    (¬ Feasible a → ∀ c : Fin (p.eval (size a)) → Bool,
      outputAfter P noOracle (extendCoins c) (enc a) (p.eval (size a)) = [0]) ∧
    (Feasible a →
      1 - 1 / (nvars a : ℚ) ≤
        ((Finset.univ.filter fun c : Fin (p.eval (size a)) → Bool =>
            Good a (outputAfter P noOracle (extendCoins c) (enc a) (p.eval (size a)))).card : ℚ)
          / 2 ^ (p.eval (size a)))

/-- The block sent to the oracle at step `t`, if the instruction at step `t` is a query. -/
def queryAt (P : Program) (O : Oracle) (c : ℕ → Bool) (I : List ℤ) (t : ℕ) : Option (List ℤ) :=
  let s := run P O c I t
  match P[s.pc]? with
  | some (.query a) => some (readBlock s.reg a (s.reg a).toNat)
  | _ => none

/-- A deterministic run of `P` on `I` (no coins, no oracle) is bounded by cost `p(|I|)` and bit
length `q(σ(I))`. -/
def DetRunOK (P : Program) (I : List ℤ) (p q : Polynomial ℕ) : Prop :=
  RunBounded P noOracle noCoins I (p.eval I.length) q 0

/-- The output of the deterministic run of `P` on `I` after `p(|I|)` steps. -/
def detOut (P : Program) (I : List ℤ) (p : Polynomial ℕ) : List ℤ :=
  outputAfter P noOracle noCoins I (p.eval I.length)

/-- Frame a list of lists as one list: each block is preceded by its length. -/
def pack : List (List ℤ) → List ℤ
  | [] => []
  | l :: ls => ((l.length : ℤ) :: l) ++ pack ls

end CongruencyTU


