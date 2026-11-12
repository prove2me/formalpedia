-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_SemidirectAut
-- name    : OddOrder_Isaacs_Ch03_SplitExtensions_SemidirectAut
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:55:45.957127+00:00
-- url     : https://prove2.me/theorems/ba8423db-331b-4592-967b-b88321c1616e
-- title:
--   Isaacs §3A: semidirect products and automorphism bounds
-- statement:
--   Covers Isaacs, *Finite Group Theory*, Chapter 3, §3A (pp. 65–74): the semidirect-product construction (Thm 3.1/3.2 as restatements of Mathlib) and the automorphism-order bounds Thm 3.3 (Horosevskii, via Ch. 2 Thm 2.20 of Lucchini) and Thm 3.4 (via Ch. 1 Thm 1.37 of Brodkey).
--
--   The one declaration is `inl_range_normal` (Thm 3.2, part 1: the image of $N$ in a semidirect product $N\rtimes H$ is normal).
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch03_SplitExtensions/SemidirectAut.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch03_SplitExtensions/SemidirectAut.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Mathlib_SchurZassenhausConj
import Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_SplitExtensionUniqueness
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh02
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable

namespace OddOrder.Isaacs.Ch03

open SemidirectProduct

open scoped Pointwise

section

variable {N H : Type*} [Group N] [Group H] (φ : H →* MulAut N)

/-- **Isaacs Thm 3.2 part 1** (半直積の正規部分群).
作用 `φ : H →* MulAut N` に対し、半直積 `N ⋊[φ] H` 内で `inl(N)` は正規部分群.

mathlib `SemidirectProduct.range_inl_eq_ker_rightHom` で `inl.range = rightHom.ker` と
書け, 核は正規. -/
instance inl_range_normal : ((inl : N →* N ⋊[φ] H)).range.Normal := by
  rw [range_inl_eq_ker_rightHom]
  infer_instance

/-- **Isaacs Thm 3.2 part 2** (半直積の補集合).
`inl(N)` と `inr(H)` は `N ⋊[φ] H` 内で互いに補集合 (`IsComplement'`).

各元 `g : N ⋊[φ] H` は `g = inl g.left * inr g.right` と一意に書ける
(`SemidirectProduct.inl_left_mul_inr_right`)。 -/
theorem inl_range_isComplement_inr_range :
    ((inl : N →* N ⋊[φ] H).range).IsComplement' ((inr : H →* N ⋊[φ] H).range) := by
  rw [Subgroup.isComplement'_def, Subgroup.isComplement_iff_bijective]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨_, n₁, rfl⟩, ⟨_, h₁, rfl⟩⟩ ⟨⟨_, n₂, rfl⟩, ⟨_, h₂, rfl⟩⟩ heq
    -- heq : inl n₁ * inr h₁ = inl n₂ * inr h₂ (in N ⋊[φ] H)
    have hL : (inl n₁ * inr h₁ : N ⋊[φ] H).left  = (inl n₂ * inr h₂ : N ⋊[φ] H).left  :=
      congrArg left heq
    have hR : (inl n₁ * inr h₁ : N ⋊[φ] H).right = (inl n₂ * inr h₂ : N ⋊[φ] H).right :=
      congrArg right heq
    simp only [mul_left, mul_right, left_inl, right_inl, left_inr, right_inr,
               map_one, mul_one, one_mul] at hL hR
    subst hL; subst hR; rfl
  · intro g
    exact ⟨(⟨inl g.left, g.left, rfl⟩, ⟨inr g.right, g.right, rfl⟩), inl_left_mul_inr_right g⟩

end

end OddOrder.Isaacs.Ch03


