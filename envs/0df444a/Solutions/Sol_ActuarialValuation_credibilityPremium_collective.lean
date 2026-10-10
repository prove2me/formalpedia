-- Prove2me | solution 1 for ActuarialValuation.credibilityPremium_collective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:42:12.310436+00:00
-- url     : https://prove2.me/submissions/ba0129e3-bc0c-4d4d-bf9a-dd627d9dda28

import Mathlib
import Definitions.Def_actuarial_credibilityPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (mu observed : ℝ) :
  credibilityPremium mu observed 0 = mu := by
  simp [credibilityPremium]
