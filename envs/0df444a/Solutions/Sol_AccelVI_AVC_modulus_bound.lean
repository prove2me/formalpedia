-- Prove2me | solution 1 for AccelVI.AVC.modulus_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:48:06.770174+00:00
-- url     : https://prove2.me/submissions/a807eee2-7777-4dec-98b5-4b3e96ef28d6

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

set_option autoImplicit false
open AccelVI.AVC

theorem solution (μ : ℝ) (hμ : μ ∈ Set.Icc (-1 : ℝ) 1) :
    1 / 2 * ‖(μ : ℂ) + 1 + Complex.I * (Real.sqrt (1 - μ ^ 2) : ℂ)‖ =
        1 / 2 * Real.sqrt ((μ + 1) ^ 2 + (Real.sqrt (1 - μ ^ 2)) ^ 2) ∧
    1 / 2 * Real.sqrt ((μ + 1) ^ 2 + (Real.sqrt (1 - μ ^ 2)) ^ 2) =
        1 / 2 * Real.sqrt 2 * Real.sqrt (1 + μ) ∧
    1 / 2 * Real.sqrt 2 * Real.sqrt (1 + μ) ≤ 1 ∧
    1 / 2 * ‖(μ : ℂ) + 1 - Complex.I * (Real.sqrt (1 - μ ^ 2) : ℂ)‖ ≤ 1 := by
  obtain ⟨h1, h2⟩ := hμ
  have hs : 0 ≤ 1 - μ ^ 2 := by nlinarith
  have hsq : (Real.sqrt (1 - μ ^ 2)) ^ 2 = 1 - μ ^ 2 := Real.sq_sqrt hs
  have hin : (μ + 1) ^ 2 + (Real.sqrt (1 - μ ^ 2)) ^ 2 = 2 * (1 + μ) := by rw [hsq]; ring
  have hn1 : ‖(μ : ℂ) + 1 + Complex.I * (Real.sqrt (1 - μ ^ 2) : ℂ)‖ =
      Real.sqrt ((μ + 1) ^ 2 + (Real.sqrt (1 - μ ^ 2)) ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp; ring
  have hn2 : ‖(μ : ℂ) + 1 - Complex.I * (Real.sqrt (1 - μ ^ 2) : ℂ)‖ =
      Real.sqrt ((μ + 1) ^ 2 + (Real.sqrt (1 - μ ^ 2)) ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp; ring
  have h2' : Real.sqrt ((μ + 1) ^ 2 + (Real.sqrt (1 - μ ^ 2)) ^ 2) = Real.sqrt 2 * Real.sqrt (1 + μ) := by
    rw [hin, Real.sqrt_mul (by norm_num)]
  have hle : Real.sqrt ((μ + 1) ^ 2 + (Real.sqrt (1 - μ ^ 2)) ^ 2) ≤ 2 := by
    rw [hin]
    calc Real.sqrt (2 * (1 + μ)) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨by rw [hn1], ?_, ?_, ?_⟩
  · rw [h2']; ring
  · rw [mul_assoc, ← h2']; linarith
  · rw [hn2]; linarith
