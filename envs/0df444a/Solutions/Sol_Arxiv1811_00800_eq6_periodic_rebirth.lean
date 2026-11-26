-- Prove2me | solution 1 for Arxiv1811_00800.eq6_periodic_rebirth
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:36:38.526922+00:00
-- url     : https://prove2.me/submissions/c6e5db70-e959-4d60-8eb3-b40a17809a84

import Mathlib
import Definitions.Def_Arxiv1811_00800_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Complex

open Arxiv1811_00800 in
theorem solution (beta : NNReal) :
    Function.Periodic (poissonEnhancement beta) (1 / 2) ∧ poissonEnhancement beta (1 / 2) = 2 := by
  have key : ∀ a : ℝ, Complex.exp (((4 * Real.pi * (a + 1 / 2) : ℝ) : ℂ) * I) =
      Complex.exp (((4 * Real.pi * a : ℝ) : ℂ) * I) := by
    intro a
    have : (((4 * Real.pi * (a + 1 / 2) : ℝ) : ℂ) * I) =
        (((4 * Real.pi * a : ℝ) : ℂ) * I) + (1 : ℤ) * (2 * Real.pi * I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  refine ⟨fun a => ?_, ?_⟩
  · unfold poissonEnhancement; rw [key]
  · unfold poissonEnhancement
    have : Complex.exp (((4 * Real.pi * (1 / 2) : ℝ) : ℂ) * I) = 1 := by
      have h := key 0
      simp only [zero_add, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h
      exact h
    rw [this]; simp; norm_num
