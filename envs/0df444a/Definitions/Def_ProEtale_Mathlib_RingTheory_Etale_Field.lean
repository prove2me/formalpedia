-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Field
-- name    : ProEtale_Mathlib_RingTheory_Etale_Field
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:39:04.144287+00:00
-- url     : https://prove2.me/theorems/c35ce20f-b2d7-52da-8a75-50d18ee1aa29
-- title:
--   The image of an algebra map from an étale algebra over a field to a local ring consists of separable elements
-- statement:
--   Let $k$ be a field, $A$ an étale $k$-algebra, $B$ a local ring that is a $k$-algebra, and $\varphi : A \to B$ a $k$-algebra homomorphism. Then for every $a \in A$, the element $\varphi(a)$ is separable over $k$, i.e. it is integral over $k$ and its minimal polynomial over $k$ is separable.
--
--   The proof writes $A$ as a finite product of finite separable field extensions of $k$ and uses that a map from such a product to a local ring factors through one factor. The lemma is used in studying ind-étale algebras over fields and residue field extensions (e.g. separability of residue fields of ind-étale algebras over a field).
--
--   **Formalization Note** The statement is `IsSeparable.of_algHom_etale_to_isLocalRing`, with `k`, `A`, `B` all in the same universe `Type u`, `[Algebra.Etale k A]`, `[IsLocalRing B]`, and conclusion `IsSeparable k (φ a)` (Mathlib's notion of a separable element).
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/Etale/Field.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Ring.Fin
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Definitions.Def_ProEtale_Mathlib_Algebra_Algebra_Pi
import Definitions.Def_ProEtale_Mathlib_RingTheory_Idempotents

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Algebra homomorphisms from an étale algebra to a local ring

The main result is `IsSeparable.of_algHom_etale_to_isLocalRing`: every element of the image
of an algebra hom from an étale algebra over a field to a local ring is separable.
-/

universe u

/-- If `A` is an étale algebra over a field `k` and `φ : A →ₐ[k] B` is an algebra homomorphism
to a local ring `B`, then every element of the image of `φ` is separable over `k`. -/
lemma IsSeparable.of_algHom_etale_to_isLocalRing (k : Type u) [Field k] (A : Type u)
    [CommRing A] [Algebra k A] [Algebra.Etale k A] (B : Type u) [CommRing B] [Algebra k B]
    [IsLocalRing B] (φ : A →ₐ[k] B) (a : A) : IsSeparable k (φ a) := by
  nontriviality B
  have : Module.Finite k A := Algebra.FormallyUnramified.finite_of_free k A
  obtain ⟨I, _, Ai, hfield, halg, e, hprop⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := k) (A := A)).mp inferInstance
  let : ∀ i, Field (Ai i) := hfield
  let : ∀ i, Algebra k (Ai i) := halg
  classical
  let ψ : (∀ i, Ai i) →ₐ[k] B := φ.comp e.symm
  obtain ⟨j, hj, hothers⟩ := ψ.exists_pi_single_eq_one_of_isLocalRing
  let τ := ψ.piFactor j hj hothers
  have hφa : φ a = τ (e a j) := by
    rw [← ψ.eq_piFactor_apply j hj hothers (e a)]
    exact (congrArg φ (e.symm_apply_apply a)).symm
  rw [hφa]
  have : Algebra.IsSeparable k (Ai j) := (hprop j).2
  have hb_sep : IsSeparable k (e a j) := Algebra.IsSeparable.isSeparable k _
  refine hb_sep.of_dvd <| minpoly.dvd k _ ?_
  rw [Polynomial.aeval_algHom_apply]
  simp [minpoly.aeval]


