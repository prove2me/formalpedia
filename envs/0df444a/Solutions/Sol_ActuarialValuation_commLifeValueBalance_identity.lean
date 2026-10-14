-- Prove2me | solution 1 for ActuarialValuation.commLifeValueBalance_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:23:10.926976+00:00
-- url     : https://prove2.me/submissions/726e7be7-2a4c-41ea-8e97-597be830a565

import Mathlib.Tactic.Ring
import Theorems.Thm_ActuarialValuation_commGrossReconciliation_zero
import Theorems.Thm_ActuarialValuation_commGrossReconciliation_succ
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commLifeValueBalance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (hD : commDiscountedLives l v x ≠ 0) : commLifeValueBalance l v x n = 1 := by
  have hg : commGrossReconciliation l v x n = commDiscountedLives l v x := by
    induction n with
    | zero => exact ActuarialValuation.commGrossReconciliation_zero l v x
    | succ n ih =>
      rw [ActuarialValuation.commGrossReconciliation_succ]
      exact ih
  unfold commLifeValueBalance commTermAssurance commTemporaryAnnuity commPureEndowment
  calc
    commDeathSum l v x n / commDiscountedLives l v x +
      commEffectiveDiscount v * (commSurvivorSum l v x n / commDiscountedLives l v x) +
      commTerminalLives l v x n / commDiscountedLives l v x =
      (commDeathSum l v x n +
       commEffectiveDiscount v * commSurvivorSum l v x n +
       commTerminalLives l v x n) / commDiscountedLives l v x := by ring
    _ = 1 := by
      change commGrossReconciliation l v x n / commDiscountedLives l v x = 1
      rw [hg]
      exact div_self hD
