-- Prove2me | solution 2 for ActuarialValuation.msSemiReserve_duration_change
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:19:22.856228+00:00
-- url     : https://prove2.me/submissions/6a3c473f-e893-48f0-b9c7-314dcfa7b11b

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msSemiReserve

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b V : Fin 3 → ℝ) (T : ℕ → Fin 3 → Fin 3 → ℝ) (v : ℝ) (d₁ d₂ : ℕ) (i : Fin 3) : msSemiReserve b T V v d₂ i - msSemiReserve b T V v d₁ i = v*(∑ j : Fin 3, (T d₂ i j-T d₁ i j)*V j) := by
  unfold msSemiReserve msSemiStep
  have hsum : (∑ j : Fin 3, (T d₂ i j - T d₁ i j) * V j) =
      (∑ j : Fin 3, T d₂ i j * V j) -
      (∑ j : Fin 3, T d₁ i j * V j) := by
        simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hsum]
  ring
