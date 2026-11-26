-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_Idempotents
-- name    : ProEtale_Mathlib_RingTheory_Idempotents
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:00:16.180496+00:00
-- url     : https://prove2.me/theorems/15c6913d-c21a-50a6-b366-2275bc7c141d
-- title:
--   Idempotents in the Jacobson radical vanish; idempotents of a local ring are 0 or 1
-- statement:
--   Let $R$ be a commutative ring and $e \in R$ an idempotent, $e^2 = e$. The file proves:
--
--   1. If $e$ lies in the Jacobson radical of $R$, then $e = 0$.
--   2. If $R$ is a local ring, then
--   $$e = 0 \quad\text{or}\quad e = 1.$$
--
--   These elementary facts are used repeatedly to deduce connectedness statements, e.g. that tensor products which are local rings have no nontrivial idempotents.
--
--   **Formalization Note** Main declarations: `IsIdempotentElem.eq_zero_of_mem_jacobson_bot` (with the Jacobson radical written as `Ideal.jacobson ⊥`) and `IsIdempotentElem.eq_zero_or_one_of_isLocalRing`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/Idempotents.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Idempotents in local rings and in the Jacobson radical

In a local ring, the only idempotent elements are `0` and `1`.
More generally, any idempotent lying in the Jacobson radical of an arbitrary
commutative ring must be zero.
-/

/-- An idempotent element of a commutative ring that lies in the Jacobson radical
(of the zero ideal) is zero. -/
lemma IsIdempotentElem.eq_zero_of_mem_jacobson_bot {R : Type*} [CommRing R]
    {e : R} (he : IsIdempotentElem e) (hmem : e ∈ Ideal.jacobson (⊥ : Ideal R)) :
    e = 0 := by
  rw [Ideal.mem_jacobson_bot] at hmem
  have hu : IsUnit (1 - e) := by simpa [mul_neg_one, neg_add_eq_sub] using hmem (-1)
  exact hu.mul_left_eq_zero.mp he.mul_one_sub_self

/-- In a local ring, every idempotent element is `0` or `1`. -/
lemma IsIdempotentElem.eq_zero_or_one_of_isLocalRing {R : Type*} [CommRing R]
    [IsLocalRing R] {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases Classical.em (e ∈ IsLocalRing.maximalIdeal R) with hmem | hnmem
  · exact .inl <| he.eq_zero_of_mem_jacobson_bot <| by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  · rw [IsLocalRing.notMem_maximalIdeal] at hnmem
    exact .inr (sub_eq_zero.mp (hnmem.mul_right_eq_zero.mp he.mul_one_sub_self)).symm


