-- Prove2me | solution 1 for ActuarialValuation.cm1ConstantForceSurvival_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:23.844957+00:00
-- url     : https://prove2.me/submissions/ec3fbbe5-3f6d-43b5-89fe-4e4b817d5ab5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ConstantForceSurvival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (μ t : ℝ) : 0 < cm1ConstantForceSurvival μ t := by
  unfold cm1ConstantForceSurvival
  exact Real.exp_pos _
