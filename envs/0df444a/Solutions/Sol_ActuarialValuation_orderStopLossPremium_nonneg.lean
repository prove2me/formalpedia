-- Prove2me | solution 1 for ActuarialValuation.orderStopLossPremium_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:41:21.864354+00:00
-- url     : https://prove2.me/submissions/b339653a-a160-4217-b2ee-ab1c3434241d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderStopLossPremium
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


open ActuarialValuation

theorem solution (w : ℕ → ℝ) (B d : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  0 ≤ orderStopLossPremium w B d := by
  show 0 ≤ (∑ s ∈ Finset.range (B + 1), ((s - d : ℕ) : ℝ) * w s)
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (Nat.cast_nonneg _) (hw s)
