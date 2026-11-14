-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.covariance_kernel_sum_and_product_psd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:31:47.308337+00:00
-- url     : https://prove2.me/submissions/5ad2674f-6390-4542-87f3-f9f9f274df03

import Mathlib
import Theorems.Thm_FamousTheorems_schur_product_theorem
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

private theorem solution_matrix_psd
    (C : ℝ → ℝ → ℝ) (hsym : ∀ s t : ℝ, C s t = C t s)
    (hpsd : ∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j * C (t i) (t j))
    (n : ℕ) (t : Fin n → ℝ) :
    (Matrix.of (fun i j : Fin n => C (t i) (t j))).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa using (hsym (t j) (t i))
  · intro a
    have h := hpsd n t a
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm] using h

theorem solution
    (C₁ C₂ : ℝ → ℝ → ℝ)
    (hsym₁ : ∀ s t : ℝ, C₁ s t = C₁ t s)
    (hsym₂ : ∀ s t : ℝ, C₂ s t = C₂ t s)
    (hpsd₁ : ∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j * C₁ (t i) (t j))
    (hpsd₂ : ∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j * C₂ (t i) (t j)) :
    (∀ s t : ℝ, C₁ s t + C₂ s t = C₁ t s + C₂ t s) ∧
    (∀ s t : ℝ, C₁ s t * C₂ s t = C₁ t s * C₂ t s) ∧
    (∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        a i * a j * (C₁ (t i) (t j) + C₂ (t i) (t j))) ∧
    (∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        a i * a j * (C₁ (t i) (t j) * C₂ (t i) (t j))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t
    rw [hsym₁ s t, hsym₂ s t]
  · intro s t
    rw [hsym₁ s t, hsym₂ s t]
  · intro n t a
    have h := add_nonneg (hpsd₁ n t a) (hpsd₂ n t a)
    simpa [mul_add, Finset.sum_add_distrib] using h
  · intro n t a
    have hM₁ := solution_matrix_psd C₁ hsym₁ hpsd₁ n t
    have hM₂ := solution_matrix_psd C₂ hsym₂ hpsd₂ n t
    have hSchur := FamousTheorems.schur_product_theorem hM₁ hM₂
    have h := Matrix.PosSemidef.dotProduct_mulVec_nonneg hSchur a
    simpa [dotProduct, Matrix.mulVec, Matrix.hadamard_apply,
      Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using h
