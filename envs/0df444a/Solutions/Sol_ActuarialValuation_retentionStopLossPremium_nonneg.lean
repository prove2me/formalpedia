-- Prove2me | solution 1 for ActuarialValuation.retentionStopLossPremium_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:24.350379+00:00
-- url     : https://prove2.me/submissions/131f061a-87eb-41f9-bd96-7be9e4556a7f

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionStopLossPremium
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w X : ℕ → ℝ) (B : ℕ) (d : ℝ)
  (hw : ∀ s, 0 ≤ w s) :
  0 ≤ retentionStopLossPremium w X B d := by
  unfold retentionStopLossPremium
  apply Finset.sum_nonneg
  intro s hs
  exact mul_nonneg (hw s) (by unfold retentionExcessPositive; exact le_max_right _ _)
