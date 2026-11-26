-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_TensorProduct_Maps
-- name    : ProEtale_Mathlib_RingTheory_TensorProduct_Maps
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:00:55.917849+00:00
-- url     : https://prove2.me/theorems/7bc4cf51-2387-5a1d-8fdf-5c4c2810b892
-- title:
--   An associativity isomorphism for tensor products of algebras over a tower of rings
-- statement:
--   Let $R \to S \to T$ be commutative rings with compatible algebra structures, let $A$ be a commutative algebra over $S$ and $T$ (compatibly with $R$), let $C$ be a commutative $S$-algebra and $D$ a commutative $R$-algebra (all with compatible scalar towers). The file defines the $T$-algebra isomorphism
--   $$(A \otimes_S C) \otimes_R D \;\xrightarrow{\ \sim\ }\; A \otimes_S (C \otimes_R D), \qquad (a \otimes c) \otimes d \mapsto a \otimes (c \otimes d),$$
--   obtained by upgrading the corresponding module associativity isomorphism to an algebra isomorphism. Simp lemmas record its underlying linear equivalence and its values on pure tensors, in both directions.
--
--   It is used to manipulate base changes of algebras, e.g. for ind-étale and weakly étale algebras.
--
--   **Formalization Note** The declaration is `Algebra.TensorProduct.assoc' R S T A C D`, with lemmas `TensorProduct.assoc'_toLinearEquiv`, `TensorProduct.assoc'_tmul`, `TensorProduct.assoc'_symm_tmul`; its underlying linear map is Mathlib's `AlgebraTensorModule.assoc R S T A C D`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/TensorProduct/Maps.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.RingTheory.TensorProduct.Maps

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
open TensorProduct

namespace Algebra


section

variable (R S T A C D : Type*) [CommRing R] [CommRing S] [CommRing T]
    [CommRing A] [CommRing C] [CommRing D] [Algebra R S] [Algebra R T] [Algebra S T]
    [Algebra R A] [Algebra R C] [Algebra R D]
    [Algebra S A] [IsScalarTower R S A] [Algebra S C] [IsScalarTower R S C]
    [Algebra T A] [IsScalarTower R T A] [IsScalarTower S T A]

def TensorProduct.assoc' :
    (A ⊗[S] C) ⊗[R] D ≃ₐ[T] A ⊗[S] (C ⊗[R] D) :=
  AlgEquiv.ofLinearEquiv
    (AlgebraTensorModule.assoc R S T A C D)
    (by simp [Algebra.TensorProduct.one_def])
    ((LinearMap.map_mul_iff _).mpr <| by ext; simp)

@[simp] theorem TensorProduct.assoc'_toLinearEquiv :
    (TensorProduct.assoc' R S T A C D).toLinearEquiv =
  AlgebraTensorModule.assoc R S T A C D := rfl

@[simp]
theorem TensorProduct.assoc'_tmul (a : A) (b : C) (c : D) :
    TensorProduct.assoc' R S T A C D ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) := rfl

@[simp]
theorem TensorProduct.assoc'_symm_tmul (a : A) (b : C) (c : D) :
    (TensorProduct.assoc' R S T A C D).symm (a ⊗ₜ (b ⊗ₜ c)) = (a ⊗ₜ b) ⊗ₜ c := rfl

end

end Algebra


