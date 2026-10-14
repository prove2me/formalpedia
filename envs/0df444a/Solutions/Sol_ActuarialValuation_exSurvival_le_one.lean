-- Prove2me | solution 1 for ActuarialValuation.exSurvival_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:43:17.694519+00:00
-- url     : https://prove2.me/submissions/9d321e99-efaf-4822-ad34-debf324ecf0d

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exSurvival
import Definitions.Def_actuarial_exBase

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma x : ℝ) (hxi : 0<xi) (hs : 0<sigma) (hx : 0≤x) : exSurvival xi sigma x≤1 := by
  unfold exSurvival
  have hnum : 0 ≤ xi * x := mul_nonneg (le_of_lt hxi) hx
  have hfrac : 0 ≤ xi * x / sigma := div_nonneg hnum (le_of_lt hs)
  have hbase1 : (1 : ℝ) ≤ exBase xi sigma x := by
    unfold exBase
    exact le_add_of_nonneg_right hfrac
  have hexp : -1 / xi ≤ (0 : ℝ) := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr zero_le_one) (le_of_lt hxi)
  exact Real.rpow_le_one_of_one_le_of_nonpos hbase1 hexp
