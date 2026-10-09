-- Prove2me | solution 1 for ActuarialValuation.finiteState_valuation_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:25:41.624742+00:00
-- url     : https://prove2.me/submissions/356ed51c-fcc2-4df1-944a-16048f904555

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
import Definitions.Def_actuarial_twoStepTransition
import Definitions.Def_actuarial_transitionRewardValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (P Q R : S → S → ℝ) (hP : isFiniteMarkovKernel P)
    (hQ : isFiniteMarkovKernel Q) (v : ℝ) (r : S → ℝ) (a d : S)
    :
    (isFiniteMarkovKernel (twoStepTransition P Q))
    ∧ (twoStepTransition (twoStepTransition P Q) R a d =
         twoStepTransition P (twoStepTransition Q R) a d)
    ∧ (transitionRewardValue P v (fun _ => 0)
         (fun b => transitionRewardValue Q v r (fun _ => 0) b) a =
         v ^ 2 * (∑ c : S, twoStepTransition P Q a c * r c)) := by
  have hkernel : isFiniteMarkovKernel (twoStepTransition P Q) := by
    constructor
    · intro a' c'
      show 0 ≤ ∑ b : S, P a' b * Q b c'
      apply Finset.sum_nonneg
      intro b _
      exact mul_nonneg (hP.1 a' b) (hQ.1 b c')
    · intro a'
      show (∑ c : S, (∑ b : S, P a' b * Q b c)) = 1
      rw [Finset.sum_comm]
      calc (∑ b : S, (∑ c : S, P a' b * Q b c))
          = ∑ b : S, P a' b * (∑ c : S, Q b c) := by
            refine Finset.sum_congr rfl (fun b _ => ?_)
            rw [Finset.mul_sum]
        _ = ∑ b : S, P a' b := by
            refine Finset.sum_congr rfl (fun b _ => ?_)
            rw [hQ.2 b, mul_one]
        _ = 1 := hP.2 a'
  have hassoc : twoStepTransition (twoStepTransition P Q) R a d =
      twoStepTransition P (twoStepTransition Q R) a d := by
    show (∑ e : S, ((∑ b : S, P a b * Q b e) * R e d)) =
        (∑ b : S, P a b * (∑ e : S, Q b e * R e d))
    calc (∑ e : S, ((∑ b : S, P a b * Q b e) * R e d))
        = (∑ e : S, (∑ b : S, P a b * Q b e * R e d)) := by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          rw [Finset.sum_mul]
      _ = (∑ b : S, (∑ e : S, P a b * Q b e * R e d)) := by
          rw [Finset.sum_comm]
      _ = (∑ b : S, P a b * (∑ e : S, Q b e * R e d)) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun e _ => ?_)
          ring
  have hA : ∀ b : S, P a b * (v * (∑ c : S, Q b c * r c)) =
      ∑ c : S, P a b * (v * (Q b c * r c)) := by
    intro b
    rw [Finset.mul_sum, Finset.mul_sum]
  have hC : ∀ c : S, ((∑ b : S, P a b * Q b c)) * (v * r c) =
      (∑ b : S, P a b * (v * (Q b c * r c))) := by
    intro c
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  have hreward : transitionRewardValue P v (fun _ => 0)
       (fun b => transitionRewardValue Q v r (fun _ => 0) b) a =
      v ^ 2 * (∑ c : S, twoStepTransition P Q a c * r c) := by
    show v * (∑ b : S, P a b * (0 + (v * (∑ c : S, Q b c * (r c + 0))))) =
      v ^ 2 * (∑ c : S, (∑ b' : S, P a b' * Q b' c) * r c)
    simp only [zero_add, add_zero]
    calc v * (∑ b : S, P a b * (v * (∑ c : S, Q b c * r c)))
        = v * (∑ b : S, (∑ c : S, P a b * (v * (Q b c * r c)))) := by
          congr 1
          exact Finset.sum_congr rfl (fun b _ => hA b)
      _ = v * (∑ c : S, (∑ b : S, P a b * (v * (Q b c * r c)))) := by
          congr 1
          rw [Finset.sum_comm]
      _ = v * (∑ c : S, ((∑ b : S, P a b * Q b c) * (v * r c))) := by
          congr 1
          exact Finset.sum_congr rfl (fun c _ => (hC c).symm)
      _ = v ^ 2 * (∑ c : S, (∑ b' : S, P a b' * Q b' c) * r c) := by
          rw [pow_two, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          ring
  exact ⟨hkernel, hassoc, hreward⟩
