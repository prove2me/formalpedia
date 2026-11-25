-- Prove2me | solution 1 for Arxiv1110_5134.phase_matrix_rotation_angles
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T07:59:04.300896+00:00
-- url     : https://prove2.me/submissions/a269e1ed-4998-43bc-880a-cd1f06a42eb4

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

private lemma stokesRot_sub_pi (φ : ℝ) : stokesRot (φ - Real.pi) = stokesRot φ := by
  have hc : Real.cos (2 * (φ - Real.pi)) = Real.cos (2 * φ) := by
    have h : 2 * φ = 2 * (φ - Real.pi) + 2 * Real.pi := by ring
    rw [h, Real.cos_add_two_pi]
  have hs : Real.sin (2 * (φ - Real.pi)) = Real.sin (2 * φ) := by
    have h : 2 * φ = 2 * (φ - Real.pi) + 2 * Real.pi := by ring
    rw [h, Real.sin_add_two_pi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stokesRot, hc, hs]

private lemma stokesRot_eq_ofCos {φ : ℝ} (hφ : φ ∈ Set.Icc 0 Real.pi) :
    stokesRot φ = stokesRotOfCos (Real.cos φ) := by
  have hsin_nn : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc hφ
  have hsqrt : Real.sqrt (1 - Real.cos φ ^ 2) = Real.sin φ := by
    have h1 : 1 - Real.cos φ ^ 2 = Real.sin φ ^ 2 := by linarith [Real.sin_sq_add_cos_sq φ]
    rw [h1, Real.sqrt_sq hsin_nn]
  have hc : Real.cos (2 * φ) = 2 * Real.cos φ ^ 2 - 1 := Real.cos_two_mul φ
  have hs : Real.sin (2 * φ) = 2 * Real.cos φ * Real.sqrt (1 - Real.cos φ ^ 2) := by
    rw [hsqrt, Real.sin_two_mul]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stokesRot, stokesRotOfCos, hc, hs]

theorem solution (P : Matrix (Fin 4) (Fin 4) ℝ) (φ φ' : ℝ)
    (hφ : φ ∈ Set.Icc 0 Real.pi) (hφ' : φ' ∈ Set.Icc 0 Real.pi) :
    stokesRot (φ - Real.pi) * P * stokesRot φ' = stokesRot φ * P * stokesRot φ' ∧
    stokesRot φ * P * stokesRot φ' =
      stokesRotOfCos (Real.cos φ) * P * stokesRotOfCos (Real.cos φ') := by
  exact ⟨by rw [stokesRot_sub_pi], by rw [stokesRot_eq_ofCos hφ, stokesRot_eq_ofCos hφ']⟩
