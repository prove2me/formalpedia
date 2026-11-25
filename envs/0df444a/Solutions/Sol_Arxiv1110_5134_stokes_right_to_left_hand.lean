-- Prove2me | solution 1 for Arxiv1110_5134.stokes_right_to_left_hand
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:01:54.862825+00:00
-- url     : https://prove2.me/submissions/4480957b-5dc2-4a2c-a5fb-d03ac356b537

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

private lemma cos_two_mul_of_tan {x : ℝ} (hx : Real.cos x ≠ 0) :
    Real.cos (2 * x) = (1 - Real.tan x ^ 2) / (1 + Real.tan x ^ 2) := by
  rw [Real.tan_eq_sin_div_cos, Real.cos_two_mul']
  have h1 : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := by linarith [Real.sin_sq_add_cos_sq x]
  have hden : 1 + (Real.sin x / Real.cos x) ^ 2 ≠ 0 := by positivity
  field_simp [hx, hden]
  nlinarith [h1]

private lemma sin_two_mul_of_tan {x : ℝ} (hx : Real.cos x ≠ 0) :
    Real.sin (2 * x) = 2 * Real.tan x / (1 + Real.tan x ^ 2) := by
  have h1 : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := by linarith [Real.sin_sq_add_cos_sq x]
  have hden : 1 + (Real.sin x / Real.cos x) ^ 2 = 1 / Real.cos x ^ 2 := by
    field_simp [hx]
    linarith [h1]
  rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul, hden]
  field_simp [hx]

theorem solution (I χ ψ χ' : ℝ) :
    (Real.tan χ ≠ 0 → Real.tan χ' = 1 / Real.tan χ →
      Real.cos (2 * χ') = -Real.cos (2 * χ) ∧ Real.sin (2 * χ') = Real.sin (2 * χ) ∧
      stokesVec I χ' (Real.pi / 2 - ψ) = handT *ᵥ stokesVec I χ ψ) ∧
    (Real.cos χ ≠ 0 → Real.cos χ' ≠ 0 → Real.tan χ' = Real.tan χ →
      stokesVec I χ' (Real.pi - ψ) = handT *ᵥ stokesVec I χ ψ) ∧
    handT * handT = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro htan htan'
    have hc : Real.cos χ ≠ 0 := by
      intro h0
      apply htan
      rw [Real.tan_eq_sin_div_cos, h0, div_zero]
    have hc' : Real.cos χ' ≠ 0 := by
      intro h0
      have htz : Real.tan χ' = 0 := by rw [Real.tan_eq_sin_div_cos, h0, div_zero]
      rw [htz] at htan'
      exact one_div_ne_zero htan htan'.symm
    have hcos : Real.cos (2 * χ') = -Real.cos (2 * χ) := by
      rw [cos_two_mul_of_tan hc', cos_two_mul_of_tan hc, htan']
      have hd1 : 1 + Real.tan χ ^ 2 ≠ 0 := by positivity
      have hd2 : 1 + (1 / Real.tan χ) ^ 2 ≠ 0 := by positivity
      field_simp [htan, hd1, hd2]
      ring
    have hsin : Real.sin (2 * χ') = Real.sin (2 * χ) := by
      rw [sin_two_mul_of_tan hc', sin_two_mul_of_tan hc, htan']
      have hd1 : 1 + Real.tan χ ^ 2 ≠ 0 := by positivity
      have hd2 : 1 + (1 / Real.tan χ) ^ 2 ≠ 0 := by positivity
      field_simp [htan, hd1, hd2]
      ring
    refine ⟨hcos, hsin, ?_⟩
    have hcψ : Real.cos (2 * (Real.pi / 2 - ψ)) = -Real.cos (2 * ψ) := by
      have : 2 * (Real.pi / 2 - ψ) = Real.pi - 2 * ψ := by ring
      rw [this, Real.cos_pi_sub]
    have hsψ : Real.sin (2 * (Real.pi / 2 - ψ)) = Real.sin (2 * ψ) := by
      have : 2 * (Real.pi / 2 - ψ) = Real.pi - 2 * ψ := by ring
      rw [this, Real.sin_pi_sub]
    ext i
    fin_cases i <;> simp [stokesVec, handT, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      hcos, hsin, hcψ, hsψ] <;> ring
  · intro hc hc' htan'
    have hcos : Real.cos (2 * χ') = Real.cos (2 * χ) := by
      rw [cos_two_mul_of_tan hc', cos_two_mul_of_tan hc, htan']
    have hsin : Real.sin (2 * χ') = Real.sin (2 * χ) := by
      rw [sin_two_mul_of_tan hc', sin_two_mul_of_tan hc, htan']
    have hcψ : Real.cos (2 * (Real.pi - ψ)) = Real.cos (2 * ψ) := by
      have : 2 * (Real.pi - ψ) = 2 * Real.pi - 2 * ψ := by ring
      rw [this, Real.cos_two_pi_sub]
    have hsψ : Real.sin (2 * (Real.pi - ψ)) = -Real.sin (2 * ψ) := by
      have : 2 * (Real.pi - ψ) = 2 * Real.pi - 2 * ψ := by ring
      rw [this, Real.sin_two_pi_sub]
    ext i
    fin_cases i <;> simp [stokesVec, handT, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      hcos, hsin, hcψ, hsψ] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [handT, Matrix.mul_apply, Fin.sum_univ_four]
