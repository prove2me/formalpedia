-- Prove2me | solution 1 for ActuarialValuation.ratExposureRatemaking_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:46:44.786984+00:00
-- url     : https://prove2.me/submissions/851cd94a-91df-45c6-a29e-4d1b4bbe0560

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_actuarial_ratWeightedExposure
import Definitions.Def_actuarial_ratPortfolioPremium
import Definitions.Def_actuarial_ratIndicatedBase
import Definitions.Def_actuarial_ratRevenueSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
    (exposure relativity : ℕ → ℝ) (n : ℕ) (target : ℝ)
    (hW : 0 < ratWeightedExposure exposure relativity n)
    (hT : 0 ≤ target) :
    (ratPortfolioPremium exposure relativity n
        (ratIndicatedBase target (ratWeightedExposure exposure relativity n)) = target) ∧
    (0 ≤ ratIndicatedBase target (ratWeightedExposure exposure relativity n)) ∧
    (ratRevenueSurplus target (ratWeightedExposure exposure relativity n)
        (ratIndicatedBase target (ratWeightedExposure exposure relativity n)) = 0) ∧
    (∀ b : ℝ,
      ratIndicatedBase target (ratWeightedExposure exposure relativity n) ≤ b →
      0 ≤ ratRevenueSurplus target (ratWeightedExposure exposure relativity n) b) := by
  let w := ratWeightedExposure exposure relativity n
  let b₀ := ratIndicatedBase target w
  have hw : 0 < w := hW
  have hbase : 0 ≤ b₀ := by
    dsimp [b₀, ratIndicatedBase]
    exact div_nonneg hT (le_of_lt hw)
  have hcancel : b₀ * w = target := by
    dsimp [b₀, ratIndicatedBase]
    exact div_mul_cancel₀ target (ne_of_gt hw)
  have hfactor (b : ℝ) :
      ratPortfolioPremium exposure relativity n b = b * w := by
    simp only [ratPortfolioPremium, ratClassPremium, ratWeightedExposure]
    calc
      (∑ i ∈ Finset.range n, exposure i * b * relativity i)
          = ∑ i ∈ Finset.range n, (exposure i * relativity i) * b := by
              apply Finset.sum_congr rfl
              intro i hi
              calc
                (exposure i * b) * relativity i
                    = exposure i * (b * relativity i) := mul_assoc _ _ _
                _ = exposure i * (relativity i * b) := by
                      rw [mul_comm b (relativity i)]
                _ = (exposure i * relativity i) * b := (mul_assoc _ _ _).symm
      _ = (∑ i ∈ Finset.range n, exposure i * relativity i) * b := by
            rw [← Finset.sum_mul]
      _ = b * ∑ i ∈ Finset.range n, exposure i * relativity i := by
            rw [mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfactor b₀]
    exact hcancel
  · exact hbase
  · dsimp [ratRevenueSurplus]
    exact sub_eq_zero.mpr hcancel
  · intro b hb
    dsimp [ratRevenueSurplus]
    apply sub_nonneg.mpr
    rw [← hcancel]
    exact mul_le_mul_of_nonneg_right hb (le_of_lt hw)
