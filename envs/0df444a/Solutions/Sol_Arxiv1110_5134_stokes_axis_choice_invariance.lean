-- Prove2me | solution 1 for Arxiv1110_5134.stokes_axis_choice_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:01:56.23983+00:00
-- url     : https://prove2.me/submissions/c2cdd0e4-b6a7-442a-9c29-593d74db0589

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

theorem solution (I χ ψ χ' : ℝ) (hχ : Real.tan χ ≠ 0)
    (hχ' : Real.tan χ' = 1 / Real.tan χ) :
    stokesVec I χ' (ψ + Real.pi / 2) = stokesVec I χ ψ := by
  have hc : Real.cos χ ≠ 0 := by
    intro h0
    apply hχ
    rw [Real.tan_eq_sin_div_cos, h0, div_zero]
  have hc' : Real.cos χ' ≠ 0 := by
    intro h0
    have htz : Real.tan χ' = 0 := by rw [Real.tan_eq_sin_div_cos, h0, div_zero]
    rw [htz] at hχ'
    exact one_div_ne_zero hχ hχ'.symm
  have hcos : Real.cos (2 * χ') = -Real.cos (2 * χ) := by
    rw [cos_two_mul_of_tan hc', cos_two_mul_of_tan hc, hχ']
    have hd1 : 1 + Real.tan χ ^ 2 ≠ 0 := by positivity
    have hd2 : 1 + (1 / Real.tan χ) ^ 2 ≠ 0 := by positivity
    field_simp [hχ, hd1, hd2]
    ring
  have hsin : Real.sin (2 * χ') = Real.sin (2 * χ) := by
    rw [sin_two_mul_of_tan hc', sin_two_mul_of_tan hc, hχ']
    have hd1 : 1 + Real.tan χ ^ 2 ≠ 0 := by positivity
    have hd2 : 1 + (1 / Real.tan χ) ^ 2 ≠ 0 := by positivity
    field_simp [hχ, hd1, hd2]
    ring
  have hcψ : Real.cos (2 * (ψ + Real.pi / 2)) = -Real.cos (2 * ψ) := by
    have : 2 * (ψ + Real.pi / 2) = 2 * ψ + Real.pi := by ring
    rw [this, Real.cos_add_pi]
  have hsψ : Real.sin (2 * (ψ + Real.pi / 2)) = -Real.sin (2 * ψ) := by
    have : 2 * (ψ + Real.pi / 2) = 2 * ψ + Real.pi := by ring
    rw [this, Real.sin_add_pi]
  ext i
  fin_cases i <;> simp [stokesVec, hcos, hsin, hcψ, hsψ] <;> ring
