-- Prove2me | solution 1 for ActuarialValuation.cm1ForceDiscount_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:27:46.363146+00:00
-- url     : https://prove2.me/submissions/876a1d2c-0173-4f1f-aed8-af1139f594b7

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ForceDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ : ℝ) : cm1ForceDiscount δ 0 = 1 := by
  simp [cm1ForceDiscount]
