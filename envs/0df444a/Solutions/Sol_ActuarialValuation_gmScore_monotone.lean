-- Prove2me | solution 1 for ActuarialValuation.gmScore_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:35:46.507182+00:00
-- url     : https://prove2.me/submissions/39c6b529-0936-4ca4-ba36-26a33a4626a9

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmScore

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claims exposure x y : ℝ) (hE : 0 ≤ exposure)
    (h : x ≤ y) : gmScore claims exposure y ≤ gmScore claims exposure x := by
  have hExp : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr h
  have hMean : exposure * Real.exp x ≤ exposure * Real.exp y :=
    mul_le_mul_of_nonneg_left hExp hE
  unfold gmScore gmMean
  linarith
