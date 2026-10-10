-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicBellmanValue_dominates_policies
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:55:44.626253+00:00
-- url     : https://prove2.me/submissions/aca2b6da-845c-46b9-9024-074e5a64dd36

import Mathlib
import Definitions.Def_actuarial_finiteEntropicBellmanValue
import Definitions.Def_actuarial_finiteEntropicPolicyValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ)
  (cost : S → A → S → ℝ) (beta gamma : ℝ)
  (terminal : S → ℝ) (n : ℕ)
  (hP : ∀ s a t, 0 ≤ P s a t)
  (hsum : ∀ s a, (∑ t : S, P s a t) = 1)
  (hbeta : 0 ≤ beta) (hgamma : 0 < gamma)
  (policy : ℕ → S → A) (s : S) :
  finiteEntropicBellmanValue P cost beta gamma terminal n s ≤
    finiteEntropicPolicyValue P cost beta gamma terminal policy n s := by
  classical
  have hmin (u : S → ℝ) (t : S) (a : A) :
      finiteEntropicBellmanMinimum P cost beta gamma u t ≤
        finiteEntropicStageCost P cost beta gamma u t a := by
    unfold finiteEntropicBellmanMinimum
    exact Finset.inf'_le
      (fun b : A => finiteEntropicStageCost P cost beta gamma u t b)
      (Finset.mem_univ a)
  have hmono (u v : S → ℝ) (t : S) (a : A)
      (huv : ∀ x, u x ≤ v x) :
      finiteEntropicStageCost P cost beta gamma u t a ≤
        finiteEntropicStageCost P cost beta gamma v t a := by
    have hmpos : 0 < finiteEntropicTransitionMoment P cost beta gamma u t a := by
      unfold finiteEntropicTransitionMoment
      by_contra hle
      have hnn : ∀ x : S,
          0 ≤ P t a x * Real.exp (gamma * (cost t a x + beta * u x)) :=
        fun x => mul_nonneg (hP t a x) (Real.exp_pos _).le
      have hzero :
          (∑ x : S, P t a x * Real.exp (gamma * (cost t a x + beta * u x))) = 0 :=
        le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun x _ => hnn x)
      have hterm : ∀ x : S,
          P t a x * Real.exp (gamma * (cost t a x + beta * u x)) = 0 := by
        intro x
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hnn x)).mp
          hzero x (Finset.mem_univ x)
      have hP0 : ∀ x : S, P t a x = 0 := by
        intro x
        exact (mul_eq_zero.mp (hterm x)).resolve_right (Real.exp_ne_zero _)
      have : (∑ x : S, P t a x) = 0 := by simp [hP0]
      exact absurd ((hsum t a).symm.trans this) one_ne_zero
    have hmle :
        finiteEntropicTransitionMoment P cost beta gamma u t a ≤
          finiteEntropicTransitionMoment P cost beta gamma v t a := by
      unfold finiteEntropicTransitionMoment
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (hP t a x)
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hgamma.le
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left (huv x) hbeta) (cost t a x)
    change Real.log (finiteEntropicTransitionMoment P cost beta gamma u t a) / gamma ≤
      Real.log (finiteEntropicTransitionMoment P cost beta gamma v t a) / gamma
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hmpos hmle) hgamma.le
  induction n generalizing s with
  | zero =>
      exact le_rfl
  | succ k ih =>
      change
        finiteEntropicBellmanMinimum P cost beta gamma
          (finiteEntropicBellmanValue P cost beta gamma terminal k) s ≤
        finiteEntropicStageCost P cost beta gamma
          (finiteEntropicPolicyValue P cost beta gamma terminal policy k)
          s (policy k s)
      exact (hmin _ s (policy k s)).trans
        (hmono _ _ s (policy k s) (fun t => ih t))
