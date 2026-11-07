-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:03:08.734586+00:00
-- url     : https://prove2.me/theorems/f5102017-70c8-4efa-ba26-3f185897d014
-- title:
--   LPSOriginal Integer Model Function Field
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integer Model Function Field, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelFunctionField.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.FunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalAffine_fractionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_cover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_openImmersion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedOverlap_agreement
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
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
lemma lpsOriginalIntegerNormalSchemeChart_integral
    (N : ℕ) (hN : 0<N) (b : Bool) :
    IsIntegral (lpsOriginalIntegerNormalSchemeChart N hN b) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b with
  | false =>
      let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
      exact inferInstanceAs (IsIntegral (Spec (.of (lpsOriginalIntegerNormalZeroChart N hN))))
  | true =>
      let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
      exact inferInstanceAs (IsIntegral (Spec (.of (lpsOriginalIntegerNormalInfinityChart N hN))))
lemma lpsOriginalIntegerNormalSchemeOverlapMap_generic
    (N : ℕ) (hN : 0<N) (b : Bool) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    letI := lpsOriginalIntegerNormalSchemeChart_integral N hN b
    lpsOriginalIntegerNormalSchemeOverlapMap N hN b
      (genericPoint (Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)))) =
      genericPoint (lpsOriginalIntegerNormalSchemeChart N hN b) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN b
  let := lpsOriginalIntegerNormalSchemeOverlapMap_openImmersion N hN b
  exact genericPoint_eq_of_isOpenImmersion _
lemma lpsOriginalIntegerNormalGluedChartMap_generic_agreement
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalIntegerNormalSchemeChart_integral N hN false
    letI := lpsOriginalIntegerNormalSchemeChart_integral N hN true
    lpsOriginalIntegerNormalGluedChartMap N hN false
      (genericPoint (lpsOriginalIntegerNormalSchemeChart N hN false)) =
    lpsOriginalIntegerNormalGluedChartMap N hN true
      (genericPoint (lpsOriginalIntegerNormalSchemeChart N hN true)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN false
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN true
  let η := genericPoint (Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)))
  have h := congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
      lpsOriginalIntegerNormalGluedScheme N hN => f η)
    (lpsOriginalIntegerNormalGluedOverlap_agreement N hN)
  dsimp only [η] at h
  simpa only [Scheme.Hom.comp_apply,
    lpsOriginalIntegerNormalSchemeOverlapMap_generic] using h
def lpsOriginalIntegerNormalGluedGenericPoint (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalGluedScheme N hN := by
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN false
  exact lpsOriginalIntegerNormalGluedChartMap N hN false
    (genericPoint (lpsOriginalIntegerNormalSchemeChart N hN false))
lemma lpsOriginalIntegerNormalGluedChartMap_generic_eq
    (N : ℕ) (hN : 0<N) (b : Bool) :
    letI := lpsOriginalIntegerNormalSchemeChart_integral N hN b
    lpsOriginalIntegerNormalGluedChartMap N hN b
      (genericPoint (lpsOriginalIntegerNormalSchemeChart N hN b)) =
      lpsOriginalIntegerNormalGluedGenericPoint N hN := by
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN b
  cases b with
  | false => rfl
  | true => exact (lpsOriginalIntegerNormalGluedChartMap_generic_agreement N hN).symm
lemma lpsOriginalIntegerNormalGluedGenericPoint_isGeneric
    (N : ℕ) (hN : 0<N) :
    IsGenericPoint (lpsOriginalIntegerNormalGluedGenericPoint N hN) Set.univ := by
  rw [isGenericPoint_iff_specializes]
  intro x
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  obtain ⟨b,y,rfl⟩ := lpsOriginalIntegerNormalGluedChartMap_cover N hN x
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN b
  have h := ((genericPoint_spec (lpsOriginalIntegerNormalSchemeChart N hN b)).specializes
    (Set.mem_univ y)).map (lpsOriginalIntegerNormalGluedChartMap N hN b).continuous
  rwa [lpsOriginalIntegerNormalGluedChartMap_generic_eq] at h
lemma lpsOriginalIntegerNormalGluedScheme_integral
    (N : ℕ) (hN : 0<N) :
    IsIntegral (lpsOriginalIntegerNormalGluedScheme N hN) := by
  let D := lpsOriginalIntegerNormalSchemeGlueData N hN
  let : ∀ b : D.openCover.I₀, IsReduced (D.openCover.X b) := fun b => by
    let := lpsOriginalIntegerNormalSchemeChart_integral N hN b
    exact inferInstanceAs (IsReduced (lpsOriginalIntegerNormalSchemeChart N hN b))
  let : IsReduced (lpsOriginalIntegerNormalGluedScheme N hN) :=
    IsReduced.of_openCover _ D.openCover
  let : IrreducibleSpace (lpsOriginalIntegerNormalGluedScheme N hN) :=
    (irreducibleSpace_def _).mpr
      (lpsOriginalIntegerNormalGluedGenericPoint_isGeneric N hN).isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced _
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def lpsOriginalIntegerNormalGluedFunctionFieldEquiv
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    (lpsOriginalIntegerNormalGluedScheme N hN).functionField ≃+*
      lpsOriginalGeneratedFunctionFieldQ N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerBaseFractionMap.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN false
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN false
  let X := lpsOriginalIntegerNormalGluedScheme N hN
  let R : CommRingCat := .of (lpsOriginalIntegerNormalZeroChart N hN)
  let : IsDomain R := inferInstanceAs (IsDomain (lpsOriginalIntegerNormalZeroChart N hN))
  let i := lpsOriginalIntegerNormalGluedChartMap N hN false
  let η := genericPoint (lpsOriginalIntegerNormalSchemeChart N hN false)
  have hη : i η=genericPoint X := genericPoint_eq_of_isOpenImmersion i
  let e := eqToIso (congrArg X.presheaf.stalk hη.symm) ≪≫ asIso (i.stalkMap η)
  let : IsFractionRing R (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    lpsOriginalIntegerNormalAffine_fractionField N hN
  let : Algebra R (Spec R).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec R
  let : IsFractionRing R (Spec R).functionField :=
    functionField_isFractionRing_of_affine R
  exact e.commRingCatIsoToRingEquiv.trans
    (IsFractionRing.ringEquivOfRingEquiv
      (K := (Spec R).functionField)
      (L := lpsOriginalGeneratedFunctionFieldQ N hN) (RingEquiv.refl R))
end
end QEC.Coding.TannerLiftedProduct


