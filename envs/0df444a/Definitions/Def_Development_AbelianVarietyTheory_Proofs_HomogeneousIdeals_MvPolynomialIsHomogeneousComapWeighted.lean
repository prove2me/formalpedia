-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:20.620951+00:00
-- url     : https://prove2.me/theorems/0270f284-30a5-4a2d-abb1-2bf598498b08
-- title:
--   Mv Polynomial Is Homogeneous Comap Weighted
-- statement:
--   Definitions and structural lemmas for Mv Polynomial Is Homogeneous Comap Weighted, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
namespace GlobalTheory.GaloisDescent
section Decomposition
variable {ι M M' σ τ : Type*} [DecidableEq ι] [AddCommMonoid M] [AddCommMonoid M']
  [SetLike σ M] [AddSubmonoidClass σ M] [SetLike τ M'] [AddSubmonoidClass τ M']
end Decomposition
section Ideals
variable {K L A B G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] [Algebra L B] [IsScalarTower K L B] {j : A →ₐ[K] B}
section Graded
variable {ι σ τ : Type*} [DecidableEq ι] [AddMonoid ι] [SetLike σ A] [AddSubmonoidClass σ A]
  [SetLike τ B] [AddSubmonoidClass τ B] (𝒜 : ι → σ) (ℬ : ι → τ) [GradedRing 𝒜] [GradedRing ℬ]
end Graded
end Ideals
section Tensor
open Algebra.TensorProduct
variable {K L A G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]
noncomputable def quotientEquivOfMapEq {A : Type*} [CommRing A] [Algebra K A] (I₀ : Ideal A)
    (I : Ideal (L ⊗[K] A)) (h : I₀.map (includeRight : A →ₐ[K] L ⊗[K] A) = I) :
    L ⊗[K] (A ⧸ I₀) ≃ₐ[L] (L ⊗[K] A) ⧸ I :=
  (tensorQuotientEquiv (R := K) L A L I₀).trans (Ideal.quotientEquivAlgOfEq L h)
end Tensor
section Polynomial
open MvPolynomial
variable {K L G σ : Type*} [Field K] [Field L] [Algebra K L]
end Polynomial
end GlobalTheory.GaloisDescent


