-- Prove2me | Definitions.Def_CubicPermFPRAS_Prog
-- name    : CubicPermFPRAS_Prog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:19.307866+00:00
-- url     : https://prove2.me/theorems/ab28c5f1-a1af-4974-9cf2-75ef7849f8ac
-- title:
--   Charged randomized programs on a uniform random tape
-- statement:
--   The algorithm is modelled as a **charged program**: it reads an infinite tape $\omega=(U_0,U_1,\dots)$ of independent $\mathrm{Uniform}[0,1]$ variables, keeps the number of operations charged so far, and aborts when a charge would exceed a budget $D$. Every uniform draw costs one operation, and every other step is charged explicitly through `tick`.
--
--   1. Probabilities of events about a run are measured with the product measure of the tape (an outer measure on arbitrary sets).
--   2. A categorical draw with weights $w$ uses one uniform $U$ and returns the least $j$ with $U\sum_iw_i<\sum_{i\le j}w_i$, which has probability $w_j/\sum_iw_i$.
--   3. A run with budget $D$ that aborts outputs $0$ and reports cost $D$; a run without a budget never aborts.
--
--   This is the paper's cost model: arithmetic operations and comparisons are counted at unit cost.
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), p.1 (PDF 3), paragraph after Corollary 2

import Mathlib

set_option autoImplicit false

namespace CubicPermFPRAS

noncomputable section

open MeasureTheory

/-- The random tape: an infinite sequence of independent `Uniform[0,1]` variables
(arXiv:2609.20717, held version sha256 9e14f335…; the paper's algorithm is randomized with
unit-cost operations, p.1 (PDF 3)). -/
abbrev Tape : Type := ℕ → unitInterval

/-- The law of the tape: the product of the uniform (Lebesgue) probability measures on
`[0,1]`. Probabilities of events about a run are measured with this (outer) measure. -/
def tapeMeasure : Measure Tape := Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)

/-- The state of a run: operations charged so far (`used`) and the next unread tape position
(`pos`). -/
structure PState where
  used : ℕ
  pos : ℕ

/-- **Charged randomized programs.** A program reads the operation budget `D ∈ ℕ∞` and the tape,
keeps a `PState`, and either returns a value or aborts (`none`) when a charge would exceed the
budget.

**Formalization Note.** This is the paper's cost model ("count arithmetic operations and
comparisons at unit cost", p.1): every primitive step of the algorithm is charged through
`tick`, and every uniform draw costs `1`. The algorithms below are total functions of the tape:
every loop has a fixed bound. -/
abbrev Prog (α : Type) : Type := ReaderT (ℕ∞ × Tape) (StateT PState Option) α

/-- Charge `c` operations; abort if the total would exceed the budget. -/
def tick (c : ℕ) : Prog Unit := do
  let env ← read
  let s ← get
  if ((s.used + c : ℕ) : ℕ∞) ≤ env.1 then set ({ s with used := s.used + c } : PState)
  else (failure : Prog Unit)

/-- Read the next uniform variable from the tape (cost `1`). -/
def unif : Prog ℝ := do
  tick 1
  let env ← read
  let s ← get
  set ({ s with pos := s.pos + 1 } : PState)
  return ((env.2 s.pos : unitInterval) : ℝ)

/-- Inverse-CDF categorical choice on one uniform `U`: the least index `j` with
`U · ∑_i w_i < ∑_{i ≤ j} w_i`. For nonnegative weights with positive total and `U < 1`, index
`j` is chosen exactly when `U ∈ [W_{<j}/S, W_{≤j}/S)`, i.e. with probability `w_j/∑_i w_i`;
`none` occurs only on a null set (`U = 1`) or for zero total weight. -/
def pickIdx {k : ℕ} (w : Fin k → ℝ) (U : ℝ) : Option (Fin k) :=
  (List.finRange k).find? fun j =>
    decide (U * ∑ i, w i < ∑ i ∈ Finset.univ.filter (fun i => i ≤ j), w i)

/-- The outcome of a run: the output value and the number of operations charged. -/
structure Result where
  out : ℝ
  cost : ℕ

/-- Run a real-valued program with budget `D` on tape `ω`. An aborted run outputs `0` and
reports cost `D` (it charged at most `D` operations before aborting). -/
def runCapped (D : ℕ) (p : Prog ℝ) (ω : Tape) : Result :=
  match p ((D : ℕ∞), ω) ⟨0, 0⟩ with
  | some (x, s) => ⟨x, s.used⟩
  | none => ⟨0, D⟩

/-- Run a program without a budget (`D = ⊤`, so it never aborts): its value and cost. -/
def runFree {α : Type} [Inhabited α] (p : Prog α) (ω : Tape) : α × ℕ :=
  match p (⊤, ω) ⟨0, 0⟩ with
  | some (x, s) => (x, s.used)
  | none => (default, 0)

/-- The law of the value of an unbudgeted program with values in a finite type, as a real
vector: `x ↦ Pr_ω[value = x]`. -/
def lawOf {α : Type} [Inhabited α] (p : Prog α) (x : α) : ℝ :=
  (tapeMeasure {ω | (runFree p ω).1 = x}).toReal

end

end CubicPermFPRAS


