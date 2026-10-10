-- Prove2me | solution 1 for ActuarialValuation.quotaShareRetainedCeded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:05:32.45262+00:00
-- url     : https://prove2.me/submissions/d67792ea-a5aa-4d20-be27-afff749f92df

import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_quotaShareRetainedClaim
import Definitions.Def_actuarial_quotaShareCededClaim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claim retention : ℝ) :
    quotaShareRetainedClaim claim retention + quotaShareCededClaim claim retention = claim := by
  dsimp [quotaShareRetainedClaim, quotaShareCededClaim]
  ring
