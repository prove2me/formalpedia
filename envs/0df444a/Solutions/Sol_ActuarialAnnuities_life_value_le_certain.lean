-- Prove2me | solution 1 for ActuarialAnnuities.life_value_le_certain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T06:17:22.098216+00:00
-- url     : https://prove2.me/submissions/f93c56a9-a85e-4fe0-99bc-facd141bef1f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bCertainPV
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAnnuities

theorem solution (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ)
    (hv : 0 ≤ v) (hb : ∀ j, 0 ≤ b j)
    (hp : ∀ k, 0 ≤ p k) (hs : bTotal h p = 1) :
    bExpectedPV h a n g delta v b p ≤
      bCertainPV h a n delta v b := by
  classical
  have hbnd (k : ℕ) :
      bPathPV h a n g delta v b k ≤ bCertainPV h a n delta v b := by
    unfold bPathPV bCertainPV
    apply Finset.sum_le_sum
    intro j hj
    by_cases hpay : a ≤ j ∧ j < a+n
    · simp only [hpay, ite_true]
      have hfactor : bEntitlement a g delta j k ≤ 1 := by
        unfold bEntitlement bAlive
        split_ifs <;> norm_num
      exact mul_le_of_le_one_right
        (mul_nonneg (hb j) (pow_nonneg hv _)) hfactor
    · simp [hpay]
  calc
    bExpectedPV h a n g delta v b p =
        ∑ k ∈ Finset.range (h+1), p k * bPathPV h a n g delta v b k := rfl
    _ ≤ ∑ k ∈ Finset.range (h+1), p k * bCertainPV h a n delta v b := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hbnd k) (hp k)
    _ = bTotal h p * bCertainPV h a n delta v b := by
      unfold bTotal
      rw [Finset.sum_mul]
    _ = bCertainPV h a n delta v b := by rw [hs]; ring
