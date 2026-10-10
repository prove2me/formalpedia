-- Prove2me | solution 1 for ActuarialValuation.quotaShareCededClaim_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:05:38.721915+00:00
-- url     : https://prove2.me/submissions/a421266f-f8f4-4007-ab00-2b79b0e24863

import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Definitions.Def_actuarial_quotaShareCededClaim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claim retention : ℝ) (hb : 0 ≤ claim)
    (hr0 : 0 ≤ retention) (hr1 : retention ≤ 1) :
    0 ≤ quotaShareCededClaim claim retention := by
  dsimp [quotaShareCededClaim]
  exact mul_nonneg (sub_nonneg.mpr hr1) hb
