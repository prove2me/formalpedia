-- Prove2me | solution 1 for Arxiv2602_07094.pauli_sq_moduli_formula
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:41:09.94881+00:00
-- url     : https://prove2.me/submissions/a101dcd7-59e5-4c4b-8918-694e862e1be4

import Mathlib
import Definitions.Def_Arxiv2602_07094_Basic

set_option autoImplicit false

open Arxiv2602_07094 in
theorem solution (S : SinclairMatrix) (hS : IsReciprocal S) :
    ‖pauliAlpha S‖ ^ 2 = (‖S 0 0‖ ^ 2 + ‖S 1 1‖ ^ 2 + 2 * (S 0 0 * star (S 1 1)).re) / 2 ∧
    ‖pauliBeta S‖ ^ 2 = (‖S 0 0‖ ^ 2 + ‖S 1 1‖ ^ 2 - 2 * (S 0 0 * star (S 1 1)).re) / 2 := by
  have h2 : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]
  unfold pauliAlpha pauliBeta
  simp only [norm_div, div_pow, h2]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_sub]
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
