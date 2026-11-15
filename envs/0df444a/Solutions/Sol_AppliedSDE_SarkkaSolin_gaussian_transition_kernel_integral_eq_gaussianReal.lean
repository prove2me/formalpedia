-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_transition_kernel_integral_eq_gaussianReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:09:28.527899+00:00
-- url     : https://prove2.me/submissions/2763f20b-eda8-4d15-a1f2-c47cb512896b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
set_option autoImplicit false
theorem solution
    (b q y h : ℝ) (hq : 0 < q) (hh : 0 < h)
    (f : ℝ -> ℝ) :
    let variance : ℝ≥0 := ⟨q * h, (mul_pos hq hh).le⟩
    (∫ x : ℝ,
      (Real.exp (-((x - y - b * h) ^ 2 / (2 * q * h))) /
        Real.sqrt (2 * Real.pi * q * h)) * f x) =
      ∫ x : ℝ, f x ∂(gaussianReal (y + b * h) variance) := by
  let variance : ℝ≥0 := ⟨q * h, (mul_pos hq hh).le⟩
  have hvpos : 0 < (variance : ℝ) := by
    change 0 < q * h
    exact mul_pos hq hh
  have hv : variance ≠ 0 := by
    intro hv0
    have hz : (variance : ℝ) = 0 := by simp [hv0]
    exact hvpos.ne' hz
  change (∫ x : ℝ,
      (Real.exp (-((x - y - b * h) ^ 2 / (2 * q * h))) /
        Real.sqrt (2 * Real.pi * q * h)) * f x) =
    ∫ x : ℝ, f x ∂(gaussianReal (y + b * h) variance)
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [gaussianPDFReal, div_eq_mul_inv]
  rw [show (variance : ℝ) = q * h from rfl]
  rw [show x - (y + b * h) = x - y - b * h by ring]
  rw [show 2 * Real.pi * (q * h) =
      2 * Real.pi * q * h by ring]
  rw [show 2 * (q * h) = 2 * q * h by ring]
  ring
