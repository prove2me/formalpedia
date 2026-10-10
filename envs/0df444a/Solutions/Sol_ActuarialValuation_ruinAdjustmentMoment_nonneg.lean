-- Prove2me | solution 1 for ActuarialValuation.ruinAdjustmentMoment_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:45:24.456082+00:00
-- url     : https://prove2.me/submissions/53438911-18aa-4048-bfc7-c8a6c3bade05

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinAdjustmentMoment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B c : ℕ) (R : ℝ)
  (hw : ∀ k, 0 ≤ w k) :
  0 ≤ ruinAdjustmentMoment w B c R := by
  unfold ruinAdjustmentMoment
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hw k) (le_of_lt (Real.exp_pos _))
