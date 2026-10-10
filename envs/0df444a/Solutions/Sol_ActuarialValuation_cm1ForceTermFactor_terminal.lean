-- Prove2me | solution 1 for ActuarialValuation.cm1ForceTermFactor_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:28:06.714862+00:00
-- url     : https://prove2.me/submissions/0c94da09-8eca-4a69-bd41-7374824a600a

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ForceTermFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ T : ℝ) : cm1ForceTermFactor δ μ T T = 0 := by
  simp [cm1ForceTermFactor]
