-- Prove2me | solution 1 for ActuarialValuation.panjerStopLoss_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:42.129379+00:00
-- url     : https://prove2.me/submissions/0c9a51e9-7523-490f-b10a-67df4444c30c

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (n : ℕ) (d : ℝ) (hg : ∀ k ∈ Finset.range (n+1), 0 ≤ g k) : 0 ≤ panjerStopLoss g n d := by
  unfold panjerStopLoss
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (le_max_right _ _) (hg k hk)
