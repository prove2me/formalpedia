-- Prove2me | solution 1 for ActuarialValuation.retentionStopLossPremium_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:33.442911+00:00
-- url     : https://prove2.me/submissions/6f2e256c-2d58-4d6a-8e5a-333d134549ca

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
  (w X : ℕ → ℝ) (B : ℕ) (a b : ℝ)
  (hw : ∀ s, 0 ≤ w s) (hab : a ≤ b) :
  retentionStopLossPremium w X B b ≤
    retentionStopLossPremium w X B a := by
  unfold retentionStopLossPremium
  apply Finset.sum_le_sum
  intro s hs
  apply mul_le_mul_of_nonneg_left _ (hw s)
  unfold retentionExcessPositive
  exact max_le_max (by linarith) (le_refl _)
