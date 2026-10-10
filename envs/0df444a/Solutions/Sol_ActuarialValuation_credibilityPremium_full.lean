-- Prove2me | solution 1 for ActuarialValuation.credibilityPremium_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:42:18.892339+00:00
-- url     : https://prove2.me/submissions/5dbd1a16-dd9e-484f-88d2-c9128546ecf8

import Mathlib
import Definitions.Def_actuarial_credibilityPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (mu observed : ℝ) :
  credibilityPremium mu observed 1 = observed := by
  simp [credibilityPremium]
