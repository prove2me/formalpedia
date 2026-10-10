-- Prove2me | solution 1 for ActuarialValuation.quotaShareVariancePremium_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:05:51.566221+00:00
-- url     : https://prove2.me/submissions/c8cb74da-3337-4d84-8d83-956c06b6b2d4

import Mathlib
import Definitions.Def_actuarial_quotaShareVariancePremium
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q claim loading : ℝ) :
    quotaShareVariancePremium q claim 0 loading =
      q * claim + loading * q * (1 - q) * claim ^ 2 := by
  simp [quotaShareVariancePremium, quotaShareCededClaim]
