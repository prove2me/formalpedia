-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicStageCost_cash_add
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:26:21.246202+00:00
-- url     : https://prove2.me/submissions/ca086952-8e1e-4472-afa0-488c67eae03c

import Mathlib
import Definitions.Def_actuarial_finiteEntropicStageCost
open ActuarialValuation

theorem solution {S A : Type*} [Fintype S]
    (P : S → A → S → ℝ) (cost : S → A → S → ℝ)
    (beta gamma : ℝ) (next : S → ℝ) (s : S) (a : A) (k : ℝ)
    (hP : ∀ t, 0 ≤ P s a t) (hsum : (∑ t : S, P s a t) = 1) (hgamma : gamma ≠ 0) :
    finiteEntropicStageCost P (fun x b t => cost x b t + k) beta gamma next s a =
      finiteEntropicStageCost P cost beta gamma next s a + k := by
  unfold finiteEntropicStageCost finiteEntropicTransitionMoment
  have hexp : ∀ t, Real.exp (gamma * ((cost s a t + k) + beta * next t)) =
      Real.exp (gamma * k) * Real.exp (gamma * (cost s a t + beta * next t)) := by
    intro t
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [hexp]
  have hmom : 0 < (∑ t : S, P s a t * Real.exp (gamma * (cost s a t + beta * next t))) := by
    by_contra hle
    have hnn : ∀ t : S, 0 ≤ P s a t * Real.exp (gamma * (cost s a t + beta * next t)) :=
      fun t => mul_nonneg (hP t) (Real.exp_pos _).le
    have hzero := le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun t _ => hnn t)
    have hterm : ∀ t, P s a t * Real.exp (gamma * (cost s a t + beta * next t)) = 0 :=
      fun t => (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hnn t)).mp hzero t (Finset.mem_univ t)
    have hP0 : ∀ t, P s a t = 0 :=
      fun t => (mul_eq_zero.mp (hterm t)).resolve_right (Real.exp_ne_zero _)
    have : (∑ t : S, P s a t) = 0 := by simp [hP0]
    exact absurd (hsum.symm.trans this) one_ne_zero
  simp_rw [mul_left_comm (P s a _) (Real.exp (gamma * k))]
  rw [← Finset.mul_sum]
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hmom), Real.log_exp]
  rw [add_div, mul_div_cancel_left₀ _ hgamma]
  ring
