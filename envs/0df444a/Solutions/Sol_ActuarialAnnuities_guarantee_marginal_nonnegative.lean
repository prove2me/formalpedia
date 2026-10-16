-- Prove2me | solution 1 for ActuarialAnnuities.guarantee_marginal_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T06:02:55.5495+00:00
-- url     : https://prove2.me/submissions/02a622fa-c952-48d2-8017-fcb2730185de

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_bSurvivalPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAnnuities

theorem solution (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ)
    (hv : 0 ≤ v) (hb : ∀ j, 0 ≤ b j) (hp : ∀ k, 0 ≤ p k) :
    bSurvivalPV h a n g delta v b p ≤
      bSurvivalPV h a n (g+1) delta v b p := by
  classical
  have hmon (t u : ℕ) (htu : t ≤ u) :
      bSurvival h p u ≤ bSurvival h p t := by
    unfold bSurvival
    apply Finset.sum_le_sum
    intro k hk
    by_cases hu : u ≤ k
    · have ht : t ≤ k := le_trans htu hu
      simp [bAlive, hu, ht]
    · by_cases ht : t ≤ k
      · simp [bAlive, hu, ht, hp k]
      · simp [bAlive, hu, ht]
  unfold bSurvivalPV
  apply Finset.sum_le_sum
  intro j hj
  by_cases hpay : a ≤ j ∧ j < a+n
  · simp only [hpay, ite_true]
    have hd : 0 ≤ b j * v^(j+delta) :=
      mul_nonneg (hb j) (pow_nonneg hv _)
    by_cases hold : j < a+g
    · have hnew : j < a+(g+1) :=
        lt_of_lt_of_le hold (Nat.add_le_add_left (Nat.le_succ g) a)
      simp [hold, hnew]
    · by_cases hnew : j < a+(g+1)
      · simp only [hold, hnew, ite_false, ite_true]
        have hage : a ≤ j+delta :=
          le_trans hpay.1 (Nat.le_add_right j delta)
        exact mul_le_mul_of_nonneg_left (hmon a (j+delta) hage) hd
      · simp [hold, hnew]
  · simp [hpay]
