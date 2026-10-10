-- Prove2me | solution 1 for ActuarialValuation.finiteHattendorffShock_expected_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:55:55.551863+00:00
-- url     : https://prove2.me/submissions/aa6e248f-288f-4cef-a1e4-c0499877db44

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Theorems.Thm_ActuarialValuation_finiteMortalityInnovation_expected_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (K : Ω → ℕ) (n : ℕ) (rho : ℕ → ℝ)
    (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t) :
    (∑ ω : Ω, w ω * finiteMortalityDiscountedShock w K rho n ω) = 0 := by
  classical
  change
    (∑ ω : Ω, w ω *
      (∑ t ∈ Finset.range n, rho t * finiteMortalityInnovation w K t ω)) = 0
  calc
    (∑ ω : Ω, w ω *
      (∑ t ∈ Finset.range n, rho t * finiteMortalityInnovation w K t ω)) =
      (∑ ω : Ω, ∑ t ∈ Finset.range n,
        w ω * (rho t * finiteMortalityInnovation w K t ω)) := by
          apply Finset.sum_congr rfl
          intro ω hω
          rw [Finset.mul_sum]
    _ = (∑ t ∈ Finset.range n, ∑ ω : Ω,
      w ω * (rho t * finiteMortalityInnovation w K t ω)) := by
        rw [Finset.sum_comm]
    _ = (∑ t ∈ Finset.range n, rho t *
      (∑ ω : Ω, w ω * finiteMortalityInnovation w K t ω)) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω hω
        ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      rw [finiteMortalityInnovation_expected_zero w K t (hS t ht)]
      ring
