-- Prove2me | solution 1 for ActuarialValuation.transitionRewardValue_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:19:38.946991+00:00
-- url     : https://prove2.me/submissions/6567a953-2b85-4fa1-96a7-1dc69c605efc

import Mathlib
import Definitions.Def_actuarial_transitionRewardValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (P : S → S → ℝ) (v c : ℝ)
    (r₁ r₂ next₁ next₂ : S → ℝ) (a : S)
    :
    transitionRewardValue P v (fun b => r₁ b + c * r₂ b)
      (fun b => next₁ b + c * next₂ b) a =
      transitionRewardValue P v r₁ next₁ a +
      c * transitionRewardValue P v r₂ next₂ a := by
  have hsum : (∑ b : S, P a b * ((r₁ b + c * r₂ b) + (next₁ b + c * next₂ b))) =
      (∑ b : S, P a b * (r₁ b + next₁ b)) +
      c * (∑ b : S, P a b * (r₂ b + next₂ b)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  show v * (∑ b : S, P a b * ((r₁ b + c * r₂ b) + (next₁ b + c * next₂ b))) =
    v * (∑ b : S, P a b * (r₁ b + next₁ b)) +
    c * (v * (∑ b : S, P a b * (r₂ b + next₂ b)))
  rw [hsum]
  ring
