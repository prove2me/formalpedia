-- Prove2me | solution 1 for ActuarialValuation.cm1ConstantForceSurvival_zero_force
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:41.554772+00:00
-- url     : https://prove2.me/submissions/90ad7aa8-d270-4b39-b977-1616f9da00cc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ConstantForceSurvival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (t : ℝ) : cm1ConstantForceSurvival 0 t = 1 := by
  simp [cm1ConstantForceSurvival]
