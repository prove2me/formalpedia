-- Prove2me | solution 1 for ActuarialValuation.cm1ForcePremiumPV_zero_premium
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:29:23.922227+00:00
-- url     : https://prove2.me/submissions/720f2857-c9db-432d-93e9-ef86c36304ad

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ForcePremiumPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ T : ℝ) : cm1ForcePremiumPV δ μ 0 T = 0 := by
  simp [cm1ForcePremiumPV]
