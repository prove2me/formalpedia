-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicTransitionMoment_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:11:45.246562+00:00
-- url     : https://prove2.me/submissions/08925fdd-4c16-441d-95c4-0be824b9634f

import Mathlib
import Definitions.Def_actuarial_finiteEntropicTransitionMoment
open ActuarialValuation

theorem solution {S A : Type*} [Fintype S]
    (P : S → A → S → ℝ) (cost : S → A → S → ℝ)
    (beta gamma : ℝ) (next : S → ℝ) (s : S) (a : A)
    (hP : ∀ t, 0 ≤ P s a t) (hsum : (∑ t : S, P s a t) = 1) :
    0 < finiteEntropicTransitionMoment P cost beta gamma next s a := by
  unfold finiteEntropicTransitionMoment
  by_contra hle
  have hnn : ∀ t : S, 0 ≤ P s a t * Real.exp (gamma * (cost s a t + beta * next t)) :=
    fun t => mul_nonneg (hP t) (Real.exp_pos _).le
  have hzero : (∑ t : S, P s a t * Real.exp (gamma * (cost s a t + beta * next t))) = 0 :=
    le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun t _ => hnn t)
  have hterm : ∀ t : S, P s a t * Real.exp (gamma * (cost s a t + beta * next t)) = 0 := by
    intro t
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hnn t)).mp hzero t (Finset.mem_univ t)
  have hP0 : ∀ t : S, P s a t = 0 := by
    intro t
    exact (mul_eq_zero.mp (hterm t)).resolve_right (Real.exp_ne_zero _)
  have : (∑ t : S, P s a t) = 0 := by simp [hP0]
  exact absurd (hsum.symm.trans this) one_ne_zero
