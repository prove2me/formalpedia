-- Prove2me | solution 1 for ActuarialValuation.commGrossReconciliation_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:17:58.189711+00:00
-- url     : https://prove2.me/submissions/28f82ad8-e38c-45cf-a32a-82c005a20467

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commGrossReconciliation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : commGrossReconciliation l v x (n+1) = commGrossReconciliation l v x n := by
  have hlocal : commDiscountedDeaths l v (x+n) +
      commEffectiveDiscount v * commDiscountedLives l v (x+n) =
      commDiscountedLives l v (x+n) -
        commDiscountedLives l v (x+n+1) := by
    unfold commDiscountedDeaths commAnnualDeaths commEffectiveDiscount commDiscountedLives
    simp only [pow_succ]
    ring
  unfold commGrossReconciliation
  simp only [commDeathSum, commSurvivorSum, commTerminalLives,
    Finset.sum_range_succ]
  simp only [← Nat.add_assoc] at *
  nlinarith [hlocal]
