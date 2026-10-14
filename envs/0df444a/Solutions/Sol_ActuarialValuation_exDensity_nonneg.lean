-- Prove2me | solution 1 for ActuarialValuation.exDensity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:41:18.536162+00:00
-- url     : https://prove2.me/submissions/2d49ef5a-e479-4d9a-9994-3ff361b329af

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exDensity
import Definitions.Def_actuarial_exSurvival
import Definitions.Def_actuarial_exHazard
import Definitions.Def_actuarial_exBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma x : ℝ) (hxi : 0<xi) (hs : 0<sigma) (hx : 0≤x) : 0≤exDensity xi sigma x := by
  unfold exDensity
  have hnum : 0 ≤ xi * x := mul_nonneg (le_of_lt hxi) hx
  have hdenom : 0 < sigma + xi * x := add_pos_of_pos_of_nonneg hs hnum
  have hfrac : 0 ≤ xi * x / sigma := div_nonneg hnum (le_of_lt hs)
  have hbase1 : (1 : ℝ) ≤ exBase xi sigma x := by
    unfold exBase
    exact le_add_of_nonneg_right hfrac
  have hbase0 : (0 : ℝ) ≤ exBase xi sigma x := le_trans zero_le_one hbase1
  have hsurv : (0 : ℝ) ≤ exSurvival xi sigma x := by
    unfold exSurvival
    exact Real.rpow_nonneg hbase0 _
  have hhaz : (0 : ℝ) ≤ exHazard xi sigma x := by
    unfold exHazard
    exact div_nonneg zero_le_one (le_of_lt hdenom)
  exact mul_nonneg hsurv hhaz
