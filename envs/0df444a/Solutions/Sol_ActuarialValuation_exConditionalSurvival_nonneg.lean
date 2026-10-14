-- Prove2me | solution 1 for ActuarialValuation.exConditionalSurvival_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:30:27.471454+00:00
-- url     : https://prove2.me/submissions/683404bc-0a79-4ba6-a069-c12e3cc9b599

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exConditionalSurvival
import Definitions.Def_actuarial_exSurvival
import Definitions.Def_actuarial_exBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma u x : ℝ) (hxi : 0<xi) (hs : 0<sigma) (hu : 0≤u) (hx : 0≤x) : 0≤exConditionalSurvival xi sigma u x := by
  unfold exConditionalSurvival
  have hux : 0 ≤ u + x := add_nonneg hu hx
  have hnum : 0 ≤ xi * (u + x) := mul_nonneg (le_of_lt hxi) hux
  have hnumfrac : 0 ≤ xi * (u + x) / sigma := div_nonneg hnum (le_of_lt hs)
  have hnum1 : (1 : ℝ) ≤ exBase xi sigma (u + x) := by
    unfold exBase
    exact le_add_of_nonneg_right hnumfrac
  have hnum0 : (0 : ℝ) ≤ exBase xi sigma (u + x) := le_trans zero_le_one hnum1
  have hden : 0 ≤ xi * u := mul_nonneg (le_of_lt hxi) hu
  have hdenfrac : 0 ≤ xi * u / sigma := div_nonneg hden (le_of_lt hs)
  have hden1 : (1 : ℝ) ≤ exBase xi sigma u := by
    unfold exBase
    exact le_add_of_nonneg_right hdenfrac
  have hden0 : (0 : ℝ) ≤ exBase xi sigma u := le_trans zero_le_one hden1
  have hsurv_num : (0 : ℝ) ≤ exSurvival xi sigma (u + x) := by
    unfold exSurvival
    exact Real.rpow_nonneg hnum0 _
  have hsurv_den : (0 : ℝ) ≤ exSurvival xi sigma u := by
    unfold exSurvival
    exact Real.rpow_nonneg hden0 _
  exact div_nonneg hsurv_num hsurv_den
