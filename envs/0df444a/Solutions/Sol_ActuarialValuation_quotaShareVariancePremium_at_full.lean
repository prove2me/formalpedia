-- Prove2me | solution 1 for ActuarialValuation.quotaShareVariancePremium_at_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:05:45.484664+00:00
-- url     : https://prove2.me/submissions/6790753d-d571-4445-9383-13fecaa5ae4f

import Mathlib
import Definitions.Def_actuarial_quotaShareVariancePremium
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q claim loading : ℝ) :
    quotaShareVariancePremium q claim 1 loading = 0 := by
  simp [quotaShareVariancePremium, quotaShareCededClaim]
