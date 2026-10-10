-- Prove2me | solution 1 for ActuarialValuation.xlRetainedVarianceNonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T14:50:15.180769+00:00
-- url     : https://prove2.me/submissions/2cf4fa1f-0c0c-4842-bf0e-ae2037b7598a

import Mathlib
import Definitions.Def_actuarial_xlRetainedVariance
open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (a : ℝ) (hw : ∀ ω, 0 ≤ w ω)
  :
  0 ≤ xlRetainedVariance w z a := by
  unfold xlRetainedVariance
  exact Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (sq_nonneg _)
