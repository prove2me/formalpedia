-- Prove2me | Definitions.Def_LevyStochCalc_Probability_AbsMoment_F000
-- name    : LevyStochCalc_Probability_AbsMoment_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:47:04.699632+00:00
-- url     : https://prove2.me/theorems/2e79b77b-4968-414c-92e4-5d27203ec80c
-- title:
--   Source declarations: LevyStochCalc.Probability.AbsMoment
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.AbsMoment. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# First absolute moment from a second-moment bound

On a probability space the first absolute moment of a real random variable is bounded by the
square root of its second moment.

## Main statements

* `LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le` — `𝔼|f| ≤ √V` whenever `𝔼f² ≤ V`.
* `LevyStochCalc.integral_abs_le_of_bounded` — `𝔼|f| ≤ K` for `|f| ≤ K`.
* `LevyStochCalc.integral_abs_add_four_le` — the triangle inequality for four summands.
-/

namespace LevyStochCalc

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- On a probability space, a measurable function bounded in absolute value by `K` is integrable
with `𝔼|f| ≤ K`. -/
theorem integral_abs_le_of_bounded {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : Measurable f) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ ω, |f ω| ≤ K) :
    Integrable f P ∧ ∫ ω, |f ω| ∂P ≤ K := by
  have hint : Integrable f P := by
    refine (integrable_const K).mono hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hK0]
    exact hK ω
  refine ⟨hint, ?_⟩
  calc ∫ ω, |f ω| ∂P ≤ ∫ _ω : Ω, K ∂P :=
        integral_mono hint.abs (integrable_const _) hK
    _ = K := by simp
end LevyStochCalc


