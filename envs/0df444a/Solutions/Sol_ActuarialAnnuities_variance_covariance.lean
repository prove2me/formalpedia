-- Prove2me | solution 1 for ActuarialAnnuities.variance_covariance
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T11:05:17.957001+00:00
-- url     : https://prove2.me/submissions/5edea6cb-dffa-4e83-87a0-742965c17f00

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bVariance
import Definitions.Def_actuarial_bCovariancePV
open ActuarialAnnuities

theorem solution(h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bVariance h a n g delta v b p = bCovariancePV h a n g delta v b p := by
  have h74 : bSecondMoment h a n g delta v b p = ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range h, if (a ≤ i ∧ i < a+n) ∧ (a ≤ j ∧ j < a+n) then (b i * v^(i+delta)) * (b j * v^(j+delta)) * bSurvival h p (max (bRequiredAge a g delta i) (bRequiredAge a g delta j)) else 0 := by
    have hE : ∀ j k, bEntitlement a g delta j k = bAlive k (bRequiredAge a g delta j) := by
      intro j k
      unfold bEntitlement bRequiredAge
      split_ifs <;> rfl
    have hA : ∀ k s t : ℕ, bAlive k s * bAlive k t = bAlive k (max s t) := by
      intro k s t
      unfold bAlive
      by_cases h1 : s ≤ k <;> by_cases h2 : t ≤ k <;> simp [h1, h2, max_le_iff]
    unfold bSecondMoment bPathPV bSurvival
    simp_rw [hE, sq, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hi : (a ≤ i ∧ i < a+n) <;> by_cases hj : (a ≤ j ∧ j < a+n) <;> simp only [hi, hj, and_self, and_false, false_and, if_true, if_false, ite_true, ite_false, mul_zero, zero_mul, Finset.sum_const_zero, and_true, true_and]
    apply Finset.sum_congr rfl
    intro k _
    rw [← hA]
    ring
  have h72 : bExpectedPV h a n g delta v b p = ∑ j ∈ Finset.range h, if a ≤ j ∧ j < a+n then b j * v^(j+delta) * bSurvival h p (bRequiredAge a g delta j) else 0 := by
    unfold bExpectedPV bPathPV bSurvival bEntitlement bRequiredAge
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> first | (simp; done) | (rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring) | (apply Finset.sum_congr rfl; intro k _; ring)
  unfold bVariance
  rw [h74, h72]
  unfold bCovariancePV
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> first | (exfalso; tauto) | ring
