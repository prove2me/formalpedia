-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke_LiteralV2Part3_QECert
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke_LiteralV2Part3_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:26:33.316218+00:00
-- url     : https://prove2.me/theorems/30694fd3-df62-454d-ad13-50ce96842cee
-- title:
--   Fricke integral construction: literal segment 3
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integral Fricke, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralFricke.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke_LiteralV2Part2_QECert
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Reverse
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerAffineToNormal_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_cover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_openImmersion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedOverlap_agreement
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToSpecZ_proper
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalBaseFractionMap_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalNormalOverlap_localization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbeddingQ_polynomial
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
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
def lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalInfinityChart N hN →+*
      lpsOriginalIntegerFrickeLocalizedNormalChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  letI := lpsOriginalIntegerFrickeLocalizedBase_scalarTower N hN
  exact
    { toFun := fun x => ⟨x.val, x.property.tower_top⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
lemma lpsOriginalIntegerFrickeLocalizedNormalChart_localization
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
    letI := (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN).toAlgebra
    IsLocalization.Away
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN)
        (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)))
      (lpsOriginalIntegerFrickeLocalizedNormalChart N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  let := lpsOriginalIntegerFrickeLocalizedBase_scalarTower N hN
  let C := lpsOriginalIntegerNormalInfinityChart N hN
  let D := lpsOriginalIntegerFrickeLocalizedNormalChart N hN
  let q := lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)
  let instCD : Algebra C D := (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN).toAlgebra
  let : SMul C D := instCD.toSMul
  let : IsScalarTower C D (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ⟨fun c d l => by
      change (c.val*d.val)*l = c.val*(d.val*l)
      exact mul_assoc _ _ _⟩
  let : IsScalarTower (Polynomial ℤ) C D := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro P
    apply Subtype.ext
    rfl
  have hq : algebraMap (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) q ≠ 0 :=
    (map_ne_zero_iff _ (lpsOriginalIntegerReciprocalBaseToGeneratedField_injective N hN)).mpr
      (lpsOriginalIntegerFrickeReciprocalDenominator_ne_zero _
        (lpsOriginalIntegerPolynomial_monic N hN))
  let : IsLocalization.Away
      (algebraMap (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) q)
      (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    IsLocalization.of_le_isUnit (fun y hy => by
      obtain ⟨n,rfl⟩ := hy
      exact (IsUnit.mk0 _ hq).pow n)
  exact IsLocalization.Away.integralClosure (R := Polynomial ℤ)
    (S := lpsOriginalGeneratedFunctionFieldQ N hN)
    (Rf := lpsOriginalIntegerFrickeLocalizedBase N hN)
    (Sf := lpsOriginalGeneratedFunctionFieldQ N hN) q
def lpsOriginalIntegerFrickeLocalizedCoefficientMap
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Polynomial ℤ →+* lpsOriginalIntegerFrickeLocalizedNormalChart N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  exact Polynomial.eval₂RingHom (Int.castRingHom _)
    ⟨(lpsOriginalRationalJNElement N hN)⁻¹,
      lpsOriginalIntegerFrickeLocalizedInverseJN_integral N hN⟩
lemma lpsOriginalIntegerFrickeLocalizedCoefficientMap_compatibility
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
    (algebraMap (lpsOriginalIntegerFrickeLocalizedNormalChart N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN)).comp
      (lpsOriginalIntegerFrickeLocalizedCoefficientMap N hN) =
    (lpsOriginalRationalFrickePullback N hN).comp
      (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  apply Polynomial.ringHom_ext
  · intro z
    simp [lpsOriginalIntegerFrickeLocalizedCoefficientMap]
  · simp only [RingHom.comp_apply, lpsOriginalIntegerFrickeLocalizedCoefficientMap,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      lpsOriginalIntegerReciprocalBaseToGeneratedField_eq_eval]
    change (lpsOriginalRationalJNElement N hN)⁻¹ =
      lpsOriginalRationalFrickePullback N hN (lpsOriginalRationalJElement N hN)⁻¹
    rw [map_inv₀, lpsOriginalRationalFrickePullback_JElement]
lemma lpsOriginalIntegerFricke_maps_normalInfinity_to_localized
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (x : lpsOriginalIntegerNormalInfinityChart N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
    IsIntegral (lpsOriginalIntegerFrickeLocalizedBase N hN)
      (lpsOriginalRationalFrickePullback N hN x.val) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  have h := IsIntegral.map_of_comp_eq (lpsOriginalIntegerFrickeLocalizedCoefficientMap N hN)
    (lpsOriginalRationalFrickePullback N hN)
    (lpsOriginalIntegerFrickeLocalizedCoefficientMap_compatibility N hN) x.property
  exact isIntegral_trans (R := lpsOriginalIntegerFrickeLocalizedBase N hN) _ h
end
end QEC.Coding.TannerLiftedProduct


