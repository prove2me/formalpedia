-- Prove2me | solution 1 for ActuarialValuation.cm1ForceDiscount_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:32:03.915706+00:00
-- url     : https://prove2.me/submissions/8826204e-eb41-47be-a6c5-c39974379b87

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ForceDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ t : ℝ) : 0 < cm1ForceDiscount δ t := by
  change 0 < Real.exp (-δ*t)
  exact Real.exp_pos _
