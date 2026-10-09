-- Prove2me | solution 1 for ActuarialValuation.transitionRewardValue_two_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:23:23.261305+00:00
-- url     : https://prove2.me/submissions/0db4b89d-e02b-4054-b8de-d42753cf7cf8

import Mathlib
import Definitions.Def_actuarial_twoStepTransition
import Definitions.Def_actuarial_transitionRewardValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (P Q : S → S → ℝ) (v : ℝ)
    (r : S → ℝ) (a : S)
    :
    transitionRewardValue P v (fun _ => 0)
       (fun b => transitionRewardValue Q v r (fun _ => 0) b) a =
      v ^ 2 * (∑ c : S, twoStepTransition P Q a c * r c) := by
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
