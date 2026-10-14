-- Prove2me | solution 1 for ActuarialValuation.exCdf_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:36:18.919283+00:00
-- url     : https://prove2.me/submissions/f02e817d-2d80-49f2-b114-91bb3b8f0760

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exCdf
import Definitions.Def_actuarial_exSurvival
import Definitions.Def_actuarial_exBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma x : ℝ) (hxi : 0<xi) (hs : 0<sigma) (hx : 0≤x) : exCdf xi sigma x≤1 := by
  unfold exCdf
  have hnum : 0 ≤ xi * x := mul_nonneg (le_of_lt hxi) hx
  have hfrac : 0 ≤ xi * x / sigma := div_nonneg hnum (le_of_lt hs)
  have hbase1 : (1 : ℝ) ≤ exBase xi sigma x := by
    unfold exBase
    exact le_add_of_nonneg_right hfrac
  have hbase0 : (0 : ℝ) ≤ exBase xi sigma x := le_trans zero_le_one hbase1
  have hs0 : (0 : ℝ) ≤ exSurvival xi sigma x := by
    unfold exSurvival
    exact Real.rpow_nonneg hbase0 _
  linarith
