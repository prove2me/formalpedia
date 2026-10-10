-- Prove2me | solution 1 for ActuarialValuation.poissonCountMass_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:27:56.023004+00:00
-- url     : https://prove2.me/submissions/c02030d3-eacc-460e-8d28-109a709ee3df

import Mathlib
import Definitions.Def_actuarial_poissonCountMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rate : ℝ) :
    poissonCountMass rate 0 = Real.exp (-rate) := by
  simp [poissonCountMass]
