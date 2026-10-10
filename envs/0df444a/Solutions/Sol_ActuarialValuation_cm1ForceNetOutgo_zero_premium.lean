-- Prove2me | solution 1 for ActuarialValuation.cm1ForceNetOutgo_zero_premium
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:32:10.174801+00:00
-- url     : https://prove2.me/submissions/b207bdcb-10b8-4ff5-9f53-17e075dc2f55

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ForceNetOutgo

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (μ B : ℝ) : cm1ForceNetOutgo μ B 0 = μ*B := by
  simp [cm1ForceNetOutgo]
