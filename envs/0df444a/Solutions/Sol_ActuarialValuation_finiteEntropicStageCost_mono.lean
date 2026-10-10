-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicStageCost_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:41:20.977562+00:00
-- url     : https://prove2.me/submissions/67dce131-840e-4c87-be58-3b8f8e59f488

import Mathlib
import Definitions.Def_actuarial_finiteEntropicStageCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S]
  (P : S → A → S → ℝ) (cost1 cost2 : S → A → S → ℝ)
  (beta gamma : ℝ) (next1 next2 : S → ℝ) (s : S) (a : A)
  (hP : ∀ t, 0 ≤ P s a t)
  (hsum : (∑ t : S, P s a t) = 1)
  (hbeta : 0 ≤ beta) (hgamma : 0 < gamma)
  (hc : ∀ t, cost1 s a t ≤ cost2 s a t)
  (hnext : ∀ t, next1 t ≤ next2 t) :
  finiteEntropicStageCost P cost1 beta gamma next1 s a ≤
  finiteEntropicStageCost P cost2 beta gamma next2 s a := by
  have hmoment_pos :
      0 < finiteEntropicTransitionMoment P cost1 beta gamma next1 s a := by
    unfold finiteEntropicTransitionMoment
    by_contra hle
    have hnn : ∀ t : S,
        0 ≤ P s a t * Real.exp (gamma * (cost1 s a t + beta * next1 t)) :=
      fun t => mul_nonneg (hP t) (Real.exp_pos _).le
    have hzero :
        (∑ t : S, P s a t * Real.exp (gamma * (cost1 s a t + beta * next1 t))) = 0 :=
      le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun t _ => hnn t)
    have hterm : ∀ t : S,
        P s a t * Real.exp (gamma * (cost1 s a t + beta * next1 t)) = 0 := by
      intro t
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hnn t)).mp
        hzero t (Finset.mem_univ t)
    have hP0 : ∀ t : S, P s a t = 0 := by
      intro t
      exact (mul_eq_zero.mp (hterm t)).resolve_right (Real.exp_ne_zero _)
    have : (∑ t : S, P s a t) = 0 := by simp [hP0]
    exact absurd (hsum.symm.trans this) one_ne_zero
  have hmoment_le :
      finiteEntropicTransitionMoment P cost1 beta gamma next1 s a ≤
        finiteEntropicTransitionMoment P cost2 beta gamma next2 s a := by
    unfold finiteEntropicTransitionMoment
    apply Finset.sum_le_sum
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (hP t)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hgamma.le
    exact add_le_add (hc t)
      (mul_le_mul_of_nonneg_left (hnext t) hbeta)
  change Real.log (finiteEntropicTransitionMoment P cost1 beta gamma next1 s a) / gamma ≤
    Real.log (finiteEntropicTransitionMoment P cost2 beta gamma next2 s a) / gamma
  exact div_le_div_of_nonneg_right
    (Real.log_le_log hmoment_pos hmoment_le) hgamma.le
