-- Prove2me | solution 1 for Arxiv1705_08274.adding_extra_relations_as_proved
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:51:29.105455+00:00
-- url     : https://prove2.me/submissions/f61be7da-ee05-4057-b3c7-648b6b805e17

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

open Arxiv1705_08274 in
theorem solution {N : ℕ} (Q₁ Q₂ Tn Rf : Matrix (Dir N) (Dir N) ℝ)
    (hw : IsUnit (wMinus Q₂ Rf).det) (hQ₁ : IsUnit Q₁.det)
    (hsym : IsSymmetricResponse (addQ Q₁ Q₂ Tn Rf)) :
    (addU Q₁ Q₂ Tn Rf).toBlocks₂₁ = Q₁⁻¹ * Tn * (addU Q₁ Q₂ Tn Rf).toBlocks₁₂ ∧
    (addU Q₁ Q₂ Tn Rf).toBlocks₂₂ = Q₁⁻¹ * (Tn * (addU Q₁ Q₂ Tn Rf).toBlocks₁₁ + Rf - Q₂) := by
  set U := addU Q₁ Q₂ Tn Rf with hUdef
  have hQ : addQ Q₁ Q₂ Tn Rf =
      fromBlocks (Q₁ * U.toBlocks₂₁) (Q₁ * U.toBlocks₂₂ + Q₂)
        (Tn * U.toBlocks₁₁ + Rf) (Tn * U.toBlocks₁₂) := by
    rw [addQ, ← hUdef]
    conv_lhs => rw [← fromBlocks_toBlocks U]
    rw [wPlus, fromBlocks_multiply, fromBlocks_add]
    simp
  obtain ⟨h1, h2⟩ := hsym
  rw [hQ] at h1 h2
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₂,
    toBlocks_fromBlocks₂₁] at h1 h2
  have hinv : Q₁⁻¹ * Q₁ = 1 := nonsing_inv_mul _ hQ₁
  constructor
  · calc U.toBlocks₂₁ = Q₁⁻¹ * (Q₁ * U.toBlocks₂₁) := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = Q₁⁻¹ * Tn * U.toBlocks₁₂ := by rw [h1, Matrix.mul_assoc]
  · calc U.toBlocks₂₂ = Q₁⁻¹ * (Q₁ * U.toBlocks₂₂ + Q₂ - Q₂) := by
          rw [add_sub_cancel_right, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = Q₁⁻¹ * (Tn * U.toBlocks₁₁ + Rf - Q₂) := by rw [h2]
