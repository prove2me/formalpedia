-- Prove2me | solution 1 for ActuarialValuation.nextStateMass_distribution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:37:02.346985+00:00
-- url     : https://prove2.me/submissions/750f2fcc-20a8-4090-aaa6-5e04d21d7ead

import Mathlib
import Definitions.Def_actuarial_isFiniteStateDistribution
import Definitions.Def_actuarial_nextStateMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (μ : S → ℝ) (P : S → S → ℝ) (hμ : isFiniteStateDistribution μ)
  (hP : (∀ i j, 0 ≤ P i j) ∧ (∀ i, (∑ j : S, P i j) = 1))
  :
  isFiniteStateDistribution (nextStateMass μ P) := by
  classical
  rcases hμ with ⟨hμ_nonneg, hμ_one⟩
  rcases hP with ⟨hP_nonneg, hP_one⟩
  constructor
  · intro j
    change 0 ≤ ∑ i : S, μ i * P i j
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (hμ_nonneg i) (hP_nonneg i j))
  · change (∑ j : S, ∑ i : S, μ i * P i j) = 1
    calc
      (∑ j : S, ∑ i : S, μ i * P i j)
          = ∑ i : S, ∑ j : S, μ i * P i j := by rw [Finset.sum_comm]
      _ = ∑ i : S, μ i * (∑ j : S, P i j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = ∑ i : S, μ i := by simp only [hP_one, mul_one]
      _ = 1 := hμ_one
