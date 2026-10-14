-- Prove2me | solution 1 for ActuarialValuation.cxHazard_ratio_reflexive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:36:47.710223+00:00
-- url     : https://prove2.me/submissions/73cf3be9-8eb7-4d6f-b07b-03b4587d79d1

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxHazardRatio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (base beta z : ℝ) (hb : base≠0) : cxHazardRatio base beta z z=1 := by
  have h : cxHazard base beta z ≠ 0 := by
    unfold cxHazard cxRelativeRisk
    exact mul_ne_zero hb (ne_of_gt (Real.exp_pos _))
  unfold cxHazardRatio
  exact div_self h
