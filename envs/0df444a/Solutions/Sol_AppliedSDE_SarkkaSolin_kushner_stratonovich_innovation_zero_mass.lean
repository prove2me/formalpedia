-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.kushner_stratonovich_innovation_zero_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:36:30.853113+00:00
-- url     : https://prove2.me/submissions/2b10d6a0-d039-4e23-a1a2-a146cac26bf8

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators

/-- The innovation gain in the Kushner-Stratonovich normalisation is
mass-neutral when the filtered probability density integrates to one. -/
theorem solution
    (n : ℕ) (p h : (Fin n → ℝ) → ℝ)
    (hpInt : Integrable p)
    (hp : ∫ x : Fin n → ℝ, p x = 1)
    (hhInt : Integrable (fun x => h x * p x)) :
    ∫ x : Fin n → ℝ,
      (h x - ∫ y : Fin n → ℝ, h y * p y) * p x = 0 := by
  let c : ℝ := ∫ y : Fin n → ℝ, h y * p y
  change ∫ x : Fin n → ℝ, (h x - c) * p x = 0
  have hsub :
      (∫ x : Fin n → ℝ, (h x - c) * p x) =
      (∫ x : Fin n → ℝ, h x * p x) -
        (∫ x : Fin n → ℝ, c * p x) := by
    simp_rw [sub_mul]
    exact integral_sub hhInt (hpInt.const_mul c)
  rw [hsub, integral_const_mul, hp]
  dsimp [c]
  ring
