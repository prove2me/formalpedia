-- Prove2me | solution 1 for ActuarialValuation.quotaShareRetainedClaim_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:18:14.266634+00:00
-- url     : https://prove2.me/submissions/d3cebf82-2fac-4e87-a3d0-554c5753b136

import Mathlib
import Definitions.Def_actuarial_quotaShareRetainedClaim
open ActuarialValuation

theorem solution (claim retention : ℝ)
  (hb : 0 ≤ claim) (hr : 0 ≤ retention) :
  0 ≤ quotaShareRetainedClaim claim retention := by
  unfold quotaShareRetainedClaim
  exact mul_nonneg hr hb
