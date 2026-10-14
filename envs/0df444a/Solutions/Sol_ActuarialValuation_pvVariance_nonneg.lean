-- Prove2me | solution 1 for ActuarialValuation.pvVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:08:27.546745+00:00
-- url     : https://prove2.me/submissions/7b9bfd81-5891-4353-8f07-64e9bffcbfb9

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvVariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p loss : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : (∑ i : Fin n, p i) = 1) : 0 ≤ pvVariance p loss := by
  let μ : ℝ := pvExpected p loss
  have hdev : 0 ≤ ∑ i : Fin n, p i * (loss i - μ)^2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hp i) (sq_nonneg _)
  have he : (∑ i : Fin n, p i * loss i) = μ := rfl
  have hsq : (∑ i : Fin n, p i * (loss i - μ)^2) =
        pvVariance p loss := by
    calc
      (∑ i : Fin n, p i * (loss i - μ)^2) =
          ∑ i : Fin n,
            (p i * loss i^2 - (2*μ) * (p i*loss i) +
              μ^2 * p i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i : Fin n, p i * loss i^2) -
            (2*μ) * (∑ i : Fin n, p i * loss i) +
            μ^2 * (∑ i : Fin n, p i) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
      _ = pvVariance p loss := by
        rw [he, hs]
        unfold pvVariance pvSecondMoment
        dsimp [μ, pvExpected]
        ring
  rw [← hsq]
  exact hdev
