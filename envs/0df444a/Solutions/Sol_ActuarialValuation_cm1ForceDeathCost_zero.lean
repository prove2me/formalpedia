-- Prove2me | solution 1 for ActuarialValuation.cm1ForceDeathCost_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:27:53.100979+00:00
-- url     : https://prove2.me/submissions/c4dc020d-000e-49f7-bb44-9cbd1c90297c

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ForceDeathCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (benefit : ℝ) : cm1ForceDeathCost 0 benefit = 0 := by
  simp [cm1ForceDeathCost]
