-- Prove2me | solution 1 for ActuarialValuation.nextStateMass_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:35:57.699268+00:00
-- url     : https://prove2.me/submissions/109bcb3a-3f4e-44eb-b65b-fe0e8654d2e8

import Mathlib
import Definitions.Def_actuarial_nextStateMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (μ : S → ℝ) (P : S → S → ℝ) (hμ : (∑ i : S, μ i) = 1) (hP : ∀ i, (∑ j : S, P i j) = 1)
  :
  (∑ j : S, nextStateMass μ P j) = 1 := by
  classical
  change (∑ j : S, ∑ i : S, μ i * P i j) = 1
  calc
    (∑ j : S, ∑ i : S, μ i * P i j)
        = ∑ i : S, ∑ j : S, μ i * P i j := by rw [Finset.sum_comm]
    _ = ∑ i : S, μ i * (∑ j : S, P i j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = ∑ i : S, μ i := by simp only [hP, mul_one]
    _ = 1 := hμ
