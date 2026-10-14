-- Prove2me | solution 1 for ActuarialValuation.commAssuranceAnnuity_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:20:36.313797+00:00
-- url     : https://prove2.me/submissions/9bca2ea7-9a8a-4483-abb2-8563955183f5

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commGrossReconciliation
import Definitions.Def_actuarial_commTermAssurance
import Definitions.Def_actuarial_commPureEndowment
import Definitions.Def_actuarial_commLifeValueBalance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (hv : 0 < v) (hl : 0 < l x) (hdec : ∀ k ∈ Finset.range n, l (x+k+1) ≤ l (x+k)) (hnonneg : 0 ≤ l (x+n)) : (commGrossReconciliation l v x n = commDiscountedLives l v x) ∧ (commLifeValueBalance l v x n = 1) ∧ (0 ≤ commTermAssurance l v x n) ∧ (0 ≤ commPureEndowment l v x n) := by
  have hD : 0 < commDiscountedLives l v x := by
    unfold commDiscountedLives
    exact mul_pos (pow_pos hv _) hl
  have hG : ∀ m : ℕ,
      commGrossReconciliation l v x m = commDiscountedLives l v x := by
    intro m
    induction m with
    | zero =>
      simp [commGrossReconciliation, commDeathSum,
        commSurvivorSum, commTerminalLives]
    | succ m ih =>
      have hlocal : commDiscountedDeaths l v (x+m) +
          commEffectiveDiscount v * commDiscountedLives l v (x+m) =
          commDiscountedLives l v (x+m) -
            commDiscountedLives l v (x+m+1) := by
        unfold commDiscountedDeaths commAnnualDeaths
          commEffectiveDiscount commDiscountedLives
        simp only [pow_succ]
        ring
      have hstep : commGrossReconciliation l v x (m+1) =
          commGrossReconciliation l v x m := by
        unfold commGrossReconciliation
        simp only [commDeathSum, commSurvivorSum, commTerminalLives,
          Finset.sum_range_succ]
        simp only [← Nat.add_assoc] at *
        nlinarith [hlocal]
      exact hstep.trans ih
  have hnum : commDeathSum l v x n +
      commEffectiveDiscount v * commSurvivorSum l v x n +
      commTerminalLives l v x n = commDiscountedLives l v x := by
    simpa only [commGrossReconciliation] using hG n
  have hL : commLifeValueBalance l v x n = 1 := by
    unfold commLifeValueBalance commTermAssurance
      commTemporaryAnnuity commPureEndowment
    calc
      commDeathSum l v x n / commDiscountedLives l v x +
          commEffectiveDiscount v * (commSurvivorSum l v x n /
            commDiscountedLives l v x) +
          commTerminalLives l v x n / commDiscountedLives l v x =
        (commDeathSum l v x n +
          commEffectiveDiscount v * commSurvivorSum l v x n +
          commTerminalLives l v x n) /
            commDiscountedLives l v x := by ring
      _ = 1 := by
        rw [hnum]
        exact div_self (ne_of_gt hD)
  have hM : 0 ≤ commDeathSum l v x n := by
    unfold commDeathSum
    apply Finset.sum_nonneg
    intro k hk
    unfold commDiscountedDeaths commAnnualDeaths
    exact mul_nonneg (pow_nonneg (le_of_lt hv) _)
      (sub_nonneg.mpr (hdec k hk))
  have hT : 0 ≤ commTerminalLives l v x n := by
    unfold commTerminalLives commDiscountedLives
    exact mul_nonneg (pow_nonneg (le_of_lt hv) _) hnonneg
  refine ⟨hG n, hL, ?_, ?_⟩
  · change 0 ≤ commDeathSum l v x n / commDiscountedLives l v x
    exact div_nonneg hM (le_of_lt hD)
  · change 0 ≤ commTerminalLives l v x n / commDiscountedLives l v x
    exact div_nonneg hT (le_of_lt hD)
