-- Prove2me | Definitions.Def_SelfSelReg_Supplement_Routine
-- name    : SelfSelReg_Supplement_Routine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:15:49.945826+00:00
-- url     : https://prove2.me/theorems/43918d18-52fc-4900-8de2-fd2cb3ebaf09
-- title:
--   Guarantee format of a randomized routine with sample access (resources on every run, success with probability $\ge 1-\delta$)
-- statement:
--   Theorems 6.1, 6.3, 7.1 and 8.1 each assert that a routine with sample access returns a correct output with probability at least $1-\delta$ and bound its sample complexity and running time. This bundle fixes the common format of such a statement, the same as in the published goal (Theorem 1.3 of the base mission).
--
--   A program $P$ of the published sampling real RAM is run on an input list, a tape of independent fair coins and an independent stream of i.i.d. samples with a given law $\mu$. The guarantee has three parts:
--
--   1. **Resources.** On every coin tape and every sample stream the run halts, having read at most a stated number of samples and performed at most a stated amount of work.
--   2. **Unconditional output properties.** A stated property holds for the output of every run.
--   3. **Success.** There is a measurable event of probability at least $1-\delta$ on which a stated property holds for the output.
--
--   The bundle also fixes the output conventions: the $j$-th returned vector of $\mathbb R^n$ and the $j$-th returned $p\times p$ matrix are read from consecutive memory cells starting at the address in pointer register $1$, and the number of returned objects of a variable-size output is the value of pointer register $2$. Vectors and matrices are written into input lists coordinate by coordinate and row by row.
--
--   **Formalization Note** The paper fixes neither an input nor an output format; these are conventions.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Theorems 6.1 and 6.3, pp.28–30 (PDF pp.31–33); Theorem 7.1, pp.48–49 (PDF pp.51–52); Theorem 8.1, p.55 (PDF p.58)

import Mathlib
import Definitions.Def_GaussMixHH_Machine

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

namespace Supplement

/-- **The guarantee of a randomized routine with sample access**, in the form of the published goal
`SelfSelReg.theorem_1_3`.

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Theorems 6.1, 6.3 (pp.28–30, PDF pp.31–33), 7.1 (pp.48–49, PDF
pp.51–52) and 8.1 (p.55, PDF p.58): "returns … with probability at least 1 − δ … Its sample complexity
is … and its running time is …".

`P` runs on the published sampling real RAM in dimension `d` from the input list `input`, on a
fair-coin tape and an independent i.i.d. stream of samples with law `μ`.
* Resources: on **every** coin tape and sample stream the run halts, having read at most `sampleBound`
  samples and done at most `workBound` work.
* `sure` holds for every halted state of every run (what the routine returns unconditionally).
* `good` holds for every halted state of the runs in a measurable event of probability at least
  `1 − δ`. -/
def RandomizedRoutine {d : ℕ} (P : GaussMixHH.Program) (input : List ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (δ sampleBound workBound : ℝ)
    (sure good : GaussMixHH.State → Prop) : Prop :=
  (∀ ω : (ℕ → Bool) × (ℕ → EuclideanSpace ℝ (Fin d)), ∃ t : ℕ,
      (GaussMixHH.run P d (GaussMixHH.initState d input) ω t).halted = true ∧
      ((GaussMixHH.run P d (GaussMixHH.initState d input) ω t).samplesUsed : ℝ) ≤ sampleBound ∧
      ((GaussMixHH.run P d (GaussMixHH.initState d input) ω t).work : ℝ) ≤ workBound) ∧
    (∀ (ω : (ℕ → Bool) × (ℕ → EuclideanSpace ℝ (Fin d))) (t : ℕ),
      (GaussMixHH.run P d (GaussMixHH.initState d input) ω t).halted = true →
      sure (GaussMixHH.run P d (GaussMixHH.initState d input) ω t)) ∧
    ∃ E : Set ((ℕ → Bool) × (ℕ → EuclideanSpace ℝ (Fin d))), MeasurableSet E ∧
      ENNReal.ofReal (1 - δ) ≤ (GaussMixHH.coinTape.prod (Measure.infinitePi fun _ : ℕ => μ)) E ∧
      ∀ ω ∈ E, ∀ t : ℕ,
        (GaussMixHH.run P d (GaussMixHH.initState d input) ω t).halted = true →
        good (GaussMixHH.run P d (GaussMixHH.initState d input) ω t)

/-- Output vector number `off` of a halted state: coordinate `j < n` is memory cell
`p[1] + off·n + j` (the layout of the published `SelfSelReg.decodeOutput`).

**Formalization Note.** The paper fixes no output format; this one is a convention. -/
noncomputable def decodeVec (n off : ℕ) (s : GaussMixHH.State) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j : Fin n => s.core.mem (s.core.ptrs 1 + (off : ℤ) * (n : ℤ) + (j : ℤ))

/-- Output matrix number `off` of a halted state, for `p × p` matrices stored one after the other
from cell `p[1]`, each row by row: entry `(i, j)` is memory cell `p[1] + off·p² + i·p + j`. -/
noncomputable def decodeMat (p off : ℕ) (s : GaussMixHH.State) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => s.core.mem (s.core.ptrs 1 + (off : ℤ) * ((p : ℤ) * (p : ℤ)) + (i : ℤ) * (p : ℤ) + (j : ℤ))

/-- The number of returned objects of a routine with a variable-size output (`i⋆` of Algorithms 6.2
and 6.4): the value of pointer register `2`. -/
def decodeCount (s : GaussMixHH.State) : ℕ := (s.core.ptrs 2).toNat

/-- A vector as the list of its coordinates. -/
noncomputable def vecData {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : List ℝ := List.ofFn fun j => v j

/-- A matrix as the list of its entries, row by row. -/
noncomputable def matData {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : List ℝ :=
  (List.ofFn fun i => List.ofFn fun j => M i j).flatten

end Supplement

end SelfSelReg


