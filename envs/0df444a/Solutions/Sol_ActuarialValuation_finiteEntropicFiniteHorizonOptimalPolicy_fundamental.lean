-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicFiniteHorizonOptimalPolicy_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:03:28.488689+00:00
-- url     : https://prove2.me/submissions/b00d7c43-8680-4e8c-9e51-0b1c87a13860

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
  (hbeta : 0 ≤ beta) (hgamma : 0 < gamma) :
  (∀ (policy : ℕ → S → A) (s : S),
    finiteEntropicBellmanValue P cost beta gamma terminal n s ≤
      finiteEntropicPolicyValue P cost beta gamma terminal policy n s)
  ∧ (∃ policy : ℕ → S → A, ∀ s : S,
      finiteEntropicPolicyValue P cost beta gamma terminal policy n s =
        finiteEntropicBellmanValue P cost beta gamma terminal n s) := by
  classical
  have hminle (u : S → ℝ) (t : S) (a : A) :
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
    exact div_le_div_of_nonneg_right (Real.log_le_log hmpos hmle) hgamma.le
  have hdom (policy : ℕ → S → A) (t : S) :
      finiteEntropicBellmanValue P cost beta gamma terminal n t ≤
        finiteEntropicPolicyValue P cost beta gamma terminal policy n t := by
    induction n generalizing t with
    | zero => exact le_rfl
    | succ k ih =>
        change finiteEntropicBellmanMinimum P cost beta gamma
            (finiteEntropicBellmanValue P cost beta gamma terminal k) t ≤
          finiteEntropicStageCost P cost beta gamma
            (finiteEntropicPolicyValue P cost beta gamma terminal policy k)
            t (policy k t)
        exact (hminle _ t (policy k t)).trans
          (hmono _ _ t (policy k t) (fun x => ih x))
  have hchoose (k : ℕ) (t : S) :
      ∃ a : A,
        finiteEntropicStageCost P cost beta gamma
          (finiteEntropicBellmanValue P cost beta gamma terminal k) t a =
        finiteEntropicBellmanMinimum P cost beta gamma
          (finiteEntropicBellmanValue P cost beta gamma terminal k) t := by
    unfold finiteEntropicBellmanMinimum
    obtain ⟨a, _, ha⟩ :=
      Finset.exists_mem_eq_inf'
        (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty)
        (fun a : A => finiteEntropicStageCost P cost beta gamma
          (finiteEntropicBellmanValue P cost beta gamma terminal k) t a)
    exact ⟨a, ha.symm⟩
  let optimal : ℕ → S → A := fun k t => Classical.choose (hchoose k t)
  have hatt :
      ∀ t : S, finiteEntropicPolicyValue P cost beta gamma terminal optimal n t =
        finiteEntropicBellmanValue P cost beta gamma terminal n t := by
    clear hdom
    induction n with
    | zero =>
        intro t
        rfl
    | succ k ih =>
        intro t
        change finiteEntropicStageCost P cost beta gamma
            (finiteEntropicPolicyValue P cost beta gamma terminal optimal k)
            t (optimal k t) =
          finiteEntropicBellmanMinimum P cost beta gamma
            (finiteEntropicBellmanValue P cost beta gamma terminal k) t
        have heq :
            finiteEntropicPolicyValue P cost beta gamma terminal optimal k =
            finiteEntropicBellmanValue P cost beta gamma terminal k := by
          funext x
          exact ih x
        rw [heq]
        exact Classical.choose_spec (hchoose k t)
  constructor
  · intro policy t
    exact hdom policy t
  · exact ⟨optimal, hatt⟩
