-- Prove2me | solution 1 for ActuarialValuation.exConditionalSurvival_start
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:32:58.523975+00:00
-- url     : https://prove2.me/submissions/381242d9-152a-4417-a5ae-d0142434a9f9

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

theorem solution (xi sigma u : ℝ) (hxi : 0<xi) (hs : 0<sigma) (hu : 0≤u) : exConditionalSurvival xi sigma u 0=1 := by
  unfold exConditionalSurvival
  have hnum : 0 ≤ xi * u := mul_nonneg (le_of_lt hxi) hu
  have hfrac : 0 ≤ xi * u / sigma := div_nonneg hnum (le_of_lt hs)
  have hbase1 : (1 : ℝ) ≤ exBase xi sigma u := by
    unfold exBase
    exact le_add_of_nonneg_right hfrac
  have hbase_pos : (0 : ℝ) < exBase xi sigma u := lt_of_lt_of_le zero_lt_one hbase1
  have hsurv_pos : (0 : ℝ) < exSurvival xi sigma u := by
    unfold exSurvival
    exact Real.rpow_pos_of_pos hbase_pos _
  have heq : u + (0 : ℝ) = u := add_zero u
  rw [heq]
  exact div_self (ne_of_gt hsurv_pos)
