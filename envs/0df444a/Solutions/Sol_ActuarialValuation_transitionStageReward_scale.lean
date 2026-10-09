-- Prove2me | solution 1 for ActuarialValuation.transitionStageReward_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:36:43.523986+00:00
-- url     : https://prove2.me/submissions/d776057c-ed17-4e67-940a-1e21602748bd

import Mathlib
import Definitions.Def_actuarial_transitionStageReward
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (μ : S → ℝ) (P : S → S → ℝ) (b : S → S → ℝ) (a : ℝ)
  :
  transitionStageReward μ P (fun i j => a * b i j) = a * transitionStageReward μ P b := by
  classical
  change (∑ i : S, ∑ j : S, μ i * P i j * (a * b i j)) =
    a * ∑ i : S, ∑ j : S, μ i * P i j * b i j
  calc
    (∑ i : S, ∑ j : S, μ i * P i j * (a * b i j))
        = ∑ i : S, ∑ j : S, a * (μ i * P i j * b i j) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = a * ∑ i : S, ∑ j : S, μ i * P i j * b i j := by
          simp only [Finset.mul_sum]
