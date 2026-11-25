-- Prove2me | solution 1 for Arxiv1705_08274.adding_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:50:19.58709+00:00
-- url     : https://prove2.me/submissions/af9c4c8e-2f42-47be-8d33-a486f025d6a1

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

open Arxiv1705_08274 in
theorem solution {N : ℕ} (Q₁ Q₂ Tn Rf : Matrix (Dir N) (Dir N) ℝ)
    (hw : IsUnit (wMinus Q₂ Rf).det)
    (I0m I0p Ilm Ilp Ilm1 Ilp1 : Dir N → ℝ)
    (hcomp : Sum.elim I0m Ilp1 = fromBlocks Q₁ Q₂ Q₂ Q₁ *ᵥ Sum.elim Ilm1 I0p)
    (hnode : Sum.elim Ilm1 Ilp = fromBlocks Tn Rf Rf Tn *ᵥ Sum.elim Ilm Ilp1) :
    Sum.elim Ilp1 Ilm1 = addU Q₁ Q₂ Tn Rf *ᵥ Sum.elim Ilm I0p ∧
    Sum.elim I0m Ilp = addQ Q₁ Q₂ Tn Rf *ᵥ Sum.elim Ilm I0p ∧
    addQ Q₁ Q₂ Tn Rf =
      fromBlocks (Q₁ * (addU Q₁ Q₂ Tn Rf).toBlocks₂₁) (Q₁ * (addU Q₁ Q₂ Tn Rf).toBlocks₂₂ + Q₂)
        (Tn * (addU Q₁ Q₂ Tn Rf).toBlocks₁₁ + Rf) (Tn * (addU Q₁ Q₂ Tn Rf).toBlocks₁₂) := by
  rw [fromBlocks_mulVec] at hcomp hnode
  have e1 : I0m = Q₁ *ᵥ Ilm1 + Q₂ *ᵥ I0p := by
    have := congrArg (· ∘ Sum.inl) hcomp; simpa using this
  have e2 : Ilp1 = Q₂ *ᵥ Ilm1 + Q₁ *ᵥ I0p := by
    have := congrArg (· ∘ Sum.inr) hcomp; simpa using this
  have e3 : Ilm1 = Tn *ᵥ Ilm + Rf *ᵥ Ilp1 := by
    have := congrArg (· ∘ Sum.inl) hnode; simpa using this
  have e4 : Ilp = Rf *ᵥ Ilm + Tn *ᵥ Ilp1 := by
    have := congrArg (· ∘ Sum.inr) hnode; simpa using this
  have hWm : wMinus Q₂ Rf *ᵥ Sum.elim Ilp1 Ilm1 = wPlus Q₁ Tn *ᵥ Sum.elim Ilm I0p := by
    rw [wMinus, wPlus, fromBlocks_mulVec, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, one_mulVec, zero_mulVec, neg_mulVec]
    congr 1
    · rw [e2]; abel
    · rw [e3]; abel
  have hU : Sum.elim Ilp1 Ilm1 = addU Q₁ Q₂ Tn Rf *ᵥ Sum.elim Ilm I0p := by
    rw [addU, ← mulVec_mulVec, ← hWm, mulVec_mulVec, nonsing_inv_mul _ hw, one_mulVec]
  refine ⟨hU, ?_, ?_⟩
  · rw [addQ, add_mulVec, ← mulVec_mulVec, ← hU, wPlus, fromBlocks_mulVec, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, zero_add, add_zero]
    rw [e1, e4, ← Sum.elim_add_add, add_comm (Rf *ᵥ Ilm)]
  · rw [addQ]
    conv_lhs => rw [← fromBlocks_toBlocks (addU Q₁ Q₂ Tn Rf)]
    rw [wPlus, fromBlocks_multiply, fromBlocks_add]
    simp
