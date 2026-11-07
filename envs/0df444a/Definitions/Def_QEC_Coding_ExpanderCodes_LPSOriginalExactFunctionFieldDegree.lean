-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:02:28.572221+00:00
-- url     : https://prove2.me/theorems/24e13dcc-2023-46f4-84a0-36b27b676629
-- title:
--   LPSOriginal Exact Function Field Degree
-- statement:
--   Definitions and structural lemmas for LPSOriginal Exact Function Field Degree, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbeddingQ_polynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbedding_polynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
def lpsOriginalHolomorphicPullback (g : 𝒮ℒ) :
    LPSOriginalHolomorphicRing ≃ₐ[ℂ] LPSOriginalHolomorphicRing where
  toFun f := ⟨fun τ => f.val (g.val⁻¹ • τ), f.property.comp
    (UpperHalfPlane.mdifferentiable_smul (by
      rw [Subgroup.HasDetOne.det_eq (inv_mem g.property)]; norm_num))⟩
  invFun f := ⟨fun τ => f.val (g.val • τ), f.property.comp
    (UpperHalfPlane.mdifferentiable_smul (by
      rw [Subgroup.HasDetOne.det_eq g.property]; norm_num))⟩
  left_inv f := by apply Subtype.ext; funext τ; simp only [inv_smul_smul]
  right_inv f := by apply Subtype.ext; funext τ; simp only [smul_inv_smul]
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
lemma lpsOriginalHolomorphicPullback_j (g : 𝒮ℒ) :
    lpsOriginalHolomorphicPullback g lpsOriginalJHolomorphic=
      lpsOriginalJHolomorphic := by
  apply Subtype.ext
  funext τ
  exact lpsOriginalJInvariant_SL_invariant _ (inv_mem g.property) τ
lemma lpsOriginalHolomorphicPullback_polynomial (g : 𝒮ℒ)
    (P : Polynomial ℂ) :
    lpsOriginalHolomorphicPullback g (lpsOriginalJHolomorphicEval P)=
      lpsOriginalJHolomorphicEval P := by
  change lpsOriginalHolomorphicPullback g
      (Polynomial.aeval lpsOriginalJHolomorphic P)=
    Polynomial.aeval lpsOriginalJHolomorphic P
  rw [←Polynomial.aeval_algHom_apply, lpsOriginalHolomorphicPullback_j]
def lpsOriginalFractionPullbackRing (g : 𝒮ℒ) :
    LPSOriginalHolomorphicFractionField ≃+* LPSOriginalHolomorphicFractionField :=
  IsFractionRing.ringEquivOfRingEquiv
    (lpsOriginalHolomorphicPullback g).toRingEquiv
lemma lpsOriginalFractionPullbackRing_localization (g : 𝒮ℒ)
    (f : LPSOriginalHolomorphicRing) :
    lpsOriginalFractionPullbackRing g
        (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField f)=
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalHolomorphicPullback g f) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ f
lemma lpsOriginalFractionPullbackRing_fixesBase (g : 𝒮ℒ)
    (x : FractionRing (Polynomial ℂ)) :
    lpsOriginalFractionPullbackRing g (lpsOriginalJFractionEmbedding x)=
      lpsOriginalJFractionEmbedding x := by
  have h : (lpsOriginalFractionPullbackRing g).toRingHom.comp
      lpsOriginalJFractionEmbedding=lpsOriginalJFractionEmbedding := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
    intro P
    change lpsOriginalFractionPullbackRing g
        (lpsOriginalJFractionEmbedding
          (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) P))=
      lpsOriginalJFractionEmbedding
        (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) P)
    rw [lpsOriginalJFractionEmbedding_polynomial,
      lpsOriginalFractionPullbackRing_localization,
      lpsOriginalHolomorphicPullback_polynomial]
  exact RingHom.congr_fun h x
def lpsOriginalFractionPullback (g : 𝒮ℒ) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    LPSOriginalHolomorphicFractionField ≃ₐ[FractionRing (Polynomial ℂ)]
      LPSOriginalHolomorphicFractionField := by
  letI := lpsOriginalJFractionEmbedding.toAlgebra
  exact { lpsOriginalFractionPullbackRing g with
    commutes' := lpsOriginalFractionPullbackRing_fixesBase g }
def lpsOriginalCosetFractionRoot (N : ℕ) (hN : 0<N)
    (x : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    LPSOriginalHolomorphicFractionField :=
  lpsOriginalFractionPullbackRing x.out (lpsOriginalJNInFractionField N hN)
lemma lpsOriginalHolomorphicPullback_polynomialQ (g : 𝒮ℒ)
    (P : Polynomial ℚ) :
    lpsOriginalHolomorphicPullback g (lpsOriginalJHolomorphicEvalQ P)=
      lpsOriginalJHolomorphicEvalQ P := by
  change lpsOriginalHolomorphicPullback g
      (lpsOriginalJHolomorphicEval (P.map (algebraMap ℚ ℂ)))=
    lpsOriginalJHolomorphicEval (P.map (algebraMap ℚ ℂ))
  exact lpsOriginalHolomorphicPullback_polynomial g _
lemma lpsOriginalFractionPullbackRing_fixesBaseQ (g : 𝒮ℒ)
    (x : FractionRing (Polynomial ℚ)) :
    lpsOriginalFractionPullbackRing g (lpsOriginalJFractionEmbeddingQ x)=
      lpsOriginalJFractionEmbeddingQ x := by
  have h : (lpsOriginalFractionPullbackRing g).toRingHom.comp
      lpsOriginalJFractionEmbeddingQ=lpsOriginalJFractionEmbeddingQ := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℚ)
    intro P
    change lpsOriginalFractionPullbackRing g
        (lpsOriginalJFractionEmbeddingQ
          (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P))=
      lpsOriginalJFractionEmbeddingQ
        (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P)
    rw [lpsOriginalJFractionEmbeddingQ_polynomial,
      lpsOriginalFractionPullbackRing_localization,
      lpsOriginalHolomorphicPullback_polynomialQ]
  exact RingHom.congr_fun h x
def lpsOriginalFractionPullbackQ (g : 𝒮ℒ) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    LPSOriginalHolomorphicFractionField ≃ₐ[FractionRing (Polynomial ℚ)]
      LPSOriginalHolomorphicFractionField := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact { lpsOriginalFractionPullbackRing g with
    commutes' := lpsOriginalFractionPullbackRing_fixesBaseQ g }
end
end QEC.Coding.TannerLiftedProduct


