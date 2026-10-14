-- Prove2me | solution 1 for ActuarialValuation.siVar_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:16:35.257094+00:00
-- url     : https://prove2.me/submissions/d5e312ba-c500-4b51-a373-1408471ceb88

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siVar

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (x : Fin m → ℝ) (hp : ∀ j, 0≤p j) (hs : (∑ j : Fin m, p j)=1) : 0≤siVar p x := by
  let μ : ℝ := siMean p x
  have hnn : 0 ≤ ∑ j : Fin m, p j * (x j - μ)^2 := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hp j) (sq_nonneg _)
  have hsumsq :
      (∑ j : Fin m, p j * (x j - μ)^2) =
      (∑ j : Fin m, p j * (x j)^2) -
        2*μ*(∑ j : Fin m, p j*x j) +
          μ^2*(∑ j : Fin m, p j) := by
    calc
      _ = ∑ j : Fin m,
          (p j*(x j)^2 - 2*μ*(p j*x j) + μ^2*p j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum]
  rw [hsumsq] at hnn
  have hmean : (∑ j : Fin m, p j*x j) = μ := rfl
  rw [hmean, hs] at hnn
  unfold siVar siSecond
  change 0 ≤ (∑ j : Fin m, p j*(x j)^2) - μ^2
  nlinarith [hnn]
