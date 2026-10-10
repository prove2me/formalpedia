-- Prove2me | solution 1 for ActuarialValuation.credibilityScaledMSE_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T13:09:36.033112+00:00
-- url     : https://prove2.me/submissions/813c859b-bfde-4f96-9cc1-78ad9ebbed6b

import Mathlib
import Definitions.Def_actuarial_credibilityScaledMSE

open ActuarialValuation

theorem solution (p epv vhm z : ℝ) (hp : 0 ≤ p) (he : 0 ≤ epv) (hv : 0 ≤ vhm) :
    0 ≤ credibilityScaledMSE p epv vhm z := by
  unfold credibilityScaledMSE
  have h1 : 0 ≤ (1 - z) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ z ^ 2 := sq_nonneg _
  exact add_nonneg (mul_nonneg (mul_nonneg hp hv) h1) (mul_nonneg he h2)
