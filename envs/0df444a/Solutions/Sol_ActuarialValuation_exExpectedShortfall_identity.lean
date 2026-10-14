-- Prove2me | solution 1 for ActuarialValuation.exExpectedShortfall_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:40:36.800017+00:00
-- url     : https://prove2.me/submissions/fd80fb44-d44c-4c48-9257-f795b5830f37

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exQuantile
import Definitions.Def_actuarial_exExpectedShortfall

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (xi sigma p : ℝ) (hxi : xi≠1) : (1-xi)*exExpectedShortfall xi sigma p=exQuantile xi sigma p+sigma := by
  have h : (1 : ℝ) - xi ≠ 0 := sub_ne_zero.mpr (Ne.symm hxi)
  unfold exExpectedShortfall
  field_simp
