-- Prove2me | solution 1 for ActuarialValuation.cm1ConstantForceSurvival_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:25.351318+00:00
-- url     : https://prove2.me/submissions/f4ae92ca-3d2b-4001-899b-9cbd3858916e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ConstantForceSurvival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (μ : ℝ) : cm1ConstantForceSurvival μ 0 = 1 := by
  simp [cm1ConstantForceSurvival]
