-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F001
-- name    : LevyStochCalc_Poisson_CharacterStrictProcess_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:57:56.45718+00:00
-- url     : https://prove2.me/theorems/3d69ba7d-ec75-4728-a3cc-f488af02a057
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterStrictProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterStrictProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterCell_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The strict-past character as a progressively measurable process

The predictable representative of the strictly-past window sum, evaluated at a fixed mark of the
window and at the time clamped to the horizon, is a jointly measurable and progressively
measurable process. For a family carried strictly before the horizon it is exactly the exponent
of the strict-past character at every time, so the strict-past character is itself progressively
measurable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Evaluation

end Evaluation

section Clamped

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  {A : Set E} {b T : ℝ}

/-- The predictable representative of the strict-past character: the exponent evaluated at a
fixed mark of the window, with the time clamped to the horizon. -/
noncomputable def charStrictPred (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ) (e₀ : E) (s : ℝ) (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * (predStrict N w Bfam A T ω (min s T) e₀ : ℂ))
theorem predStrict_of_nonpos (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ) {s : ℝ}
    (hs : s ≤ 0) (e : E) (ω : Ω) : predStrict N w Bfam A T ω s e = 0 := by
  classical
  have hzero : ∀ C : Set (ℝ × E), strictCount N C A T ω s e = 0 := by
    intro C
    refine le_antisymm (iSup_le fun n => le_of_eq ?_) (by positivity)
    refine Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (fun hmem => ?_) _
    have h1 : ((i : ℝ) / 2 ^ n) < s := hmem.1.1
    have h2 : (0 : ℝ) ≤ (i : ℝ) / 2 ^ n := by positivity
    linarith
  simp [predStrict, hzero]
variable (hℱ : IsPoissonFiltration N ℱ) (hBm : ∀ j, MeasurableSet (Bfam j))
  (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)

section Parts

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ)

end Parts

end Clamped

end LevyStochCalc.Poisson


