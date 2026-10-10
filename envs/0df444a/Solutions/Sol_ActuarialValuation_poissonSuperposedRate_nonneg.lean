-- Prove2me | solution 1 for ActuarialValuation.poissonSuperposedRate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T13:07:01.580761+00:00
-- url     : https://prove2.me/submissions/8e27d572-978e-4d62-b57c-c9ad9e73f650

import Mathlib
import Definitions.Def_actuarial_poissonSuperposedRate

open ActuarialValuation

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ poissonSuperposedRate a b := by
  unfold poissonSuperposedRate
  exact add_nonneg ha hb
