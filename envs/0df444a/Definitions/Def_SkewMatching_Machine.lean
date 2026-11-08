-- Prove2me | Definitions.Def_SkewMatching_Machine
-- name    : SkewMatching_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:07:46.05426+00:00
-- url     : https://prove2.me/theorems/b10ad81b-0fd5-4b7b-8129-71b704856ebc
-- title:
--   The word RAM with fair coins: programs, runs, word bound, coin tape
-- statement:
--   A **program** is a finite list of instructions together with a word exponent $c$. The machine has integer registers and a memory addressed by integers, all initialised to $0$ except the input cells. The instructions are: integer literals, $+$, $-$, $\times$, floor division $\lfloor a/b\rfloor$, shifts $a\cdot 2^b$ and $\lfloor a/2^b\rfloor$, bit length, load, store, the jump "if $a\le b$ go to $\ell$", `coin d` (which writes the next bit of an infinite tape $\tau\in\{0,1\}^{\mathbb N}$ to a register), and `halt`.
--
--   Every executed instruction costs one step. On an input with size parameter $B$ the **word bound** is $W=B^c$: an integer result, memory address or shift amount outside $[-W,W]$ sends the machine to a **stuck** state, which never halts; an invalid program counter is stuck as well. Halted and stuck states repeat forever, so the running time on a tape is the index of the first halted state. The tape law is the product of fair coins on $\{0,1\}^{\mathbb N}$.
--
--   This is the model in which "we can compute" of Theorem 1, Theorem 2 and Lemma 11 is read.
--
--   **Formalization Note** The paper names no machine. The exponent $c$ is part of the program and is chosen before the input, so a word holds $O(\log n)$ bits. No instruction carries a function or a real number.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Theorem 1, p.1 (machine not named in the paper)

import Mathlib

namespace SkewMatching

open MeasureTheory

/-!
# The word RAM with fair coins

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript
sha256 3fc151f5…). The paper names no machine for "we can compute" in Theorem 1, p.1, Theorem 2, p.1
and Lemma 11, p.5.

A program is a finite list of instructions, together with a word exponent `wordExp`. Registers are
`ℕ → ℤ`, memory is `ℤ → ℤ`. Instructions: integer literal, `+`, `−`, `×`, floor division `⌊a/b⌋`
(with `⌊a/0⌋ = 0`), shifts `a·2^b` and `⌊a/2^b⌋`, bit length, load, store, the jump "if `a ≤ b` go to
`target`", `coin d` (writes the next fair bit of the tape to register `d`) and `halt`.

**Formalization Note.**
* No constructor carries a function or a real number, so a program is a finite syntactic object.
* **Word bound.** `step` takes the word bound `W`; each theorem fixes `W = (n+2)^wordExp`, with
  `wordExp` chosen with the program, before the input. An integer result, a memory address or a shift
  amount outside `[−W, W]` sends the machine to a stuck state, which never halts. Hence a word holds
  `O(log n)` bits and unit-cost multiplication cannot hide a large computation.
* **Cost.** Every executed instruction, including `coin` and `halt`, is one step. A halted state and a
  stuck state stutter, so the running time is the index of the first halted state. An invalid program
  counter is stuck.
-/

namespace Machine

/-- An instruction. Register indices and jump targets are natural numbers. -/
inductive Instr : Type
  | iconst (d : ℕ) (k : ℤ)
  | iadd (d a b : ℕ)
  | isub (d a b : ℕ)
  | imul (d a b : ℕ)
  | idiv (d a b : ℕ)
  | ishl (d a b : ℕ)
  | ishr (d a b : ℕ)
  | ibitlen (d a : ℕ)
  | iload (d a : ℕ)
  | istore (a b : ℕ)
  | ijle (a b target : ℕ)
  | coin (d : ℕ)
  | halt
  deriving DecidableEq

/-- A program: a finite instruction list and the word exponent of its word bound. -/
structure Program : Type where
  code : List Instr
  wordExp : ℕ

/-- A machine state. `cursor` is the position of the next unread bit of the coin tape. -/
structure State : Type where
  pc : ℕ
  reg : ℕ → ℤ
  mem : ℤ → ℤ
  cursor : ℕ
  halted : Bool
  stuck : Bool

/-- The word bound `W = B^wordExp` of the program `P` on an input of size parameter `B`. -/
def wordBound (P : Program) (B : ℕ) : ℤ := (B : ℤ) ^ P.wordExp

/-- `z` fits in a word: `−W ≤ z ≤ W`. -/
def Fits (W z : ℤ) : Prop := -W ≤ z ∧ z ≤ W

instance (W z : ℤ) : Decidable (Fits W z) := by unfold Fits; infer_instance

/-- The stuck state reached from `σ`. -/
def State.toStuck (σ : State) : State := { σ with stuck := true }

/-- Write the integer `v` to register `d` and advance, or get stuck if `v` does not fit. -/
def setReg (W : ℤ) (σ : State) (d : ℕ) (v : ℤ) : State :=
  if Fits W v then { σ with reg := Function.update σ.reg d v, pc := σ.pc + 1 } else σ.toStuck

/-- Execute one instruction under word bound `W`, reading coins from the tape `τ`. -/
def exec1 (W : ℤ) (τ : ℕ → Bool) (σ : State) : Instr → State
  | .iconst d k => setReg W σ d k
  | .iadd d a b => setReg W σ d (σ.reg a + σ.reg b)
  | .isub d a b => setReg W σ d (σ.reg a - σ.reg b)
  | .imul d a b => setReg W σ d (σ.reg a * σ.reg b)
  | .idiv d a b => setReg W σ d (Int.fdiv (σ.reg a) (σ.reg b))
  | .ishl d a b =>
      if 0 ≤ σ.reg b ∧ σ.reg b ≤ W then setReg W σ d (σ.reg a * 2 ^ (σ.reg b).toNat)
      else σ.toStuck
  | .ishr d a b =>
      if 0 ≤ σ.reg b ∧ σ.reg b ≤ W then setReg W σ d (Int.fdiv (σ.reg a) (2 ^ (σ.reg b).toNat))
      else σ.toStuck
  | .ibitlen d a => setReg W σ d (Nat.size (σ.reg a).natAbs)
  | .iload d a => if Fits W (σ.reg a) then setReg W σ d (σ.mem (σ.reg a)) else σ.toStuck
  | .istore a b =>
      if Fits W (σ.reg a) then
        { σ with mem := Function.update σ.mem (σ.reg a) (σ.reg b), pc := σ.pc + 1 }
      else σ.toStuck
  | .ijle a b target =>
      if σ.reg a ≤ σ.reg b then { σ with pc := target } else { σ with pc := σ.pc + 1 }
  | .coin d =>
      { σ with reg := Function.update σ.reg d (if τ σ.cursor then 1 else 0),
               pc := σ.pc + 1, cursor := σ.cursor + 1 }
  | .halt => { σ with halted := true }

/-- One step. Halted and stuck states stutter; an invalid program counter is stuck. -/
def step (P : Program) (W : ℤ) (τ : ℕ → Bool) (σ : State) : State :=
  if σ.halted || σ.stuck then σ else
    match P.code[σ.pc]? with
    | none => σ.toStuck
    | some ins => exec1 W τ σ ins

/-- The initial state with the given memory: registers `0`, program counter `0`, tape cursor `0`. -/
def initState (mem : ℤ → ℤ) : State where
  pc := 0
  reg := fun _ => 0
  mem := mem
  cursor := 0
  halted := false
  stuck := false

/-- The state after `T` steps of `P` from `σ₀`, under word bound `W` and coin tape `τ`. -/
def run (P : Program) (W : ℤ) (τ : ℕ → Bool) (σ₀ : State) (T : ℕ) : State :=
  (step P W τ)^[T] σ₀

/-- The law of the coin tape: i.i.d. fair bits. -/
noncomputable def coinTape : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

/-- `P` has halted within `T` steps from `σ₀` on the tape `τ`. -/
def HaltsWithin (P : Program) (W : ℤ) (τ : ℕ → Bool) (σ₀ : State) (T : ℕ) : Prop :=
  (run P W τ σ₀ T).halted = true

/-- Cells `base + 2j`, `base + 2j + 1` hold the two entries of the `j`-th pair of `l`; every other cell
holds `0`. The input layouts of the mission use this. -/
def pairCells (base : ℤ) (l : List (ℕ × ℕ)) (a : ℤ) : ℤ :=
  if a < base then 0 else
    match l[(a - base).toNat / 2]? with
    | none => 0
    | some p => if (a - base).toNat % 2 = 0 then (p.1 : ℤ) else (p.2 : ℤ)

end Machine

end SkewMatching


