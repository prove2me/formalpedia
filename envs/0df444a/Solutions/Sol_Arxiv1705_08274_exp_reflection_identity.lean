-- Prove2me | solution 1 for Arxiv1705_08274.exp_reflection_identity
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:52:32.841812+00:00
-- url     : https://prove2.me/submissions/8161a8a4-46fa-4d8e-9edd-372d8e10782e

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

open Arxiv1705_08274 in
theorem solution {N : ℕ} (S : DOModel N) (hS : S.Admissible)
    (h : ℝ) (hh : 0 < h) :
    NormedSpace.exp (h • S.jacobian) = nodeExp S.jacobian (-h) ∧
    nodeExp S.jacobian (-h) =
      fromBlocks (nodeExp S.jacobian h).toBlocks₂₂ (nodeExp S.jacobian h).toBlocks₂₁
        (nodeExp S.jacobian h).toBlocks₁₂ (nodeExp S.jacobian h).toBlocks₁₁ := by
  have h1 : NormedSpace.exp (h • S.jacobian) = nodeExp S.jacobian (-h) := by
    rw [nodeExp, neg_smul, neg_neg]
  refine ⟨h1, ?_⟩
  rw [← h1]
  set P : Matrix (Dir N ⊕ Dir N) (Dir N ⊕ Dir N) ℝ := fromBlocks 0 1 1 0 with hP
  have hPP : P * P = 1 := by
    rw [hP, fromBlocks_multiply]; simp [fromBlocks_one]
  have hPinv : P⁻¹ = P := Matrix.inv_eq_left_inv hPP
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hPP)
  have hconj : P * (-(h • S.jacobian)) * P⁻¹ = h • S.jacobian := by
    rw [hPinv, hP, DOModel.jacobian]
    simp [fromBlocks_multiply, fromBlocks_smul, fromBlocks_neg]
  rw [← hconj, Matrix.exp_conj _ _ hPu, hPinv, ← nodeExp]
  set E := nodeExp S.jacobian h
  conv_lhs => rw [← fromBlocks_toBlocks E]
  rw [hP, fromBlocks_multiply, fromBlocks_multiply]
  simp
