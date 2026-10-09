-- Prove2me | solution 1 for ActuarialValuation.transitionStageReward_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:36:49.710568+00:00
-- url     : https://prove2.me/submissions/25217c7d-09b0-4ba4-918f-6c83fe87ffa3

import Mathlib
import Definitions.Def_actuarial_transitionStageReward
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (μ : S → ℝ) (P : S → S → ℝ) (hμ : (∑ i : S, μ i) = 1)
  (hP : ∀ i, (∑ j : S, P i j) = 1) (a : ℝ)
  :
  transitionStageReward μ P (fun _ _ => a) = a := by
  classical
  change (∑ i : S, ∑ j : S, μ i * P i j * a) = a
  calc
    (∑ i : S, ∑ j : S, μ i * P i j * a)
        = ∑ i : S, μ i * (∑ j : S, P i j) * a := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            (∑ j : S, μ i * P i j * a)
                = (∑ j : S, μ i * P i j) * a := by rw [Finset.sum_mul]
            _ = μ i * (∑ j : S, P i j) * a := by rw [Finset.mul_sum]
    _ = ∑ i : S, μ i * a := by simp only [hP, mul_one]
    _ = (∑ i : S, μ i) * a := by rw [Finset.sum_mul]
    _ = a := by rw [hμ]; ring
