-- Prove2me | solution 1 for ActuarialValuation.aggregateConvolution_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T14:50:09.080205+00:00
-- url     : https://prove2.me/submissions/ccbfedff-d693-4257-aa7e-da529b9990f9

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution
open ActuarialValuation

theorem solution (f g : ℕ → ℝ) (s : ℕ)
  (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k) :
  0 ≤ aggregateConvolution f g s := by
  unfold aggregateConvolution
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hf k) (hg (s - k))
