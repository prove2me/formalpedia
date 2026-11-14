-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.zakai_unnormalised_density_recovers_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:44:05.76331+00:00
-- url     : https://prove2.me/submissions/8efead2e-c3ed-4e70-b17e-61f417d4689d

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators

/-- Normalising a nonnegative integrable Zakai density gives a probability
density and the corresponding normalised expectation functional. -/
theorem solution
    (n : ℕ) (q : (Fin n → ℝ) → ℝ)
    (hqn : ∀ x, 0 ≤ q x) (hqInt : Integrable q)
    (hZ : 0 < ∫ x, q x) :
    let Z : ℝ := ∫ x : Fin n → ℝ, q x
    let p : (Fin n → ℝ) → ℝ := fun x => q x / Z
    (∀ x, 0 ≤ p x) ∧
    (∫ x : Fin n → ℝ, p x = 1) ∧
    (∀ φ : (Fin n → ℝ) → ℝ,
      Integrable (fun x => φ x * q x) →
      ∫ x : Fin n → ℝ, φ x * p x =
        (∫ x : Fin n → ℝ, φ x * q x) / Z) := by
  let Z : ℝ := ∫ x : Fin n → ℝ, q x
  let p : (Fin n → ℝ) → ℝ := fun x => q x / Z
  change (∀ x, 0 ≤ p x) ∧ (∫ x : Fin n → ℝ, p x = 1) ∧
    (∀ φ : (Fin n → ℝ) → ℝ,
      Integrable (fun x => φ x * q x) →
      ∫ x : Fin n → ℝ, φ x * p x =
        (∫ x : Fin n → ℝ, φ x * q x) / Z)
  have hZne : Z ≠ 0 := ne_of_gt hZ
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact div_nonneg (hqn x) hZ.le
  · change (∫ x : Fin n → ℝ, q x / Z) = 1
    simp only [div_eq_mul_inv, integral_mul_const]
    exact mul_inv_cancel₀ hZne
  · intro φ hφq
    change (∫ x : Fin n → ℝ, φ x * (q x / Z)) =
      (∫ x : Fin n → ℝ, φ x * q x) / Z
    have heq :
        (fun x : Fin n → ℝ => φ x * (q x / Z)) =
          (fun x => (φ x * q x) / Z) := by
      funext x
      ring
    rw [heq]
    simp only [div_eq_mul_inv, integral_mul_const]
