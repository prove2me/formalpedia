-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:09:39.245876+00:00
-- url     : https://prove2.me/theorems/20356da1-9981-4d03-9edb-ff35939a0b47
-- title:
--   LPSOriginal Generic Differential Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Generic Differential Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGenericDifferentialComparison.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finiteDimensional
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicToMeromorphicGerm_constant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbedding_polynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJMeromorphicDerivative_ne_zero
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
open scoped TensorProduct
noncomputable section
section GenericDifferential
variable (N : ℕ) (hpos : 0 < N)
local instance _p2m_local_instance_6f8db27f7a_31 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance _p2m_local_instance_6f8db27f7a_37 : Algebra P K :=
  ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance _p2m_local_instance_6f8db27f7a_39 : Algebra ℂ K :=
  ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance _p2m_local_instance_6f8db27f7a_41 : IsScalarTower P J K := IsScalarTower.of_algebraMap_eq' rfl
local instance _p2m_local_instance_6f8db27f7a_42 : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local instance _p2m_local_instance_6f8db27f7a_43 : IsScalarTower ℂ P K := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap J K (algebraMap ℂ J c) =
    algebraMap J K (algebraMap P J (algebraMap ℂ P c))
  rw [IsScalarTower.algebraMap_apply ℂ P J]
lemma lpsOriginalGenericComplexConstant_value (c : ℂ) :
    (algebraMap ℂ K c).val = algebraMap ℂ LPSOriginalHolomorphicFractionField c := by
  change lpsOriginalJFractionEmbedding (algebraMap ℂ J c) = _
  rw [IsScalarTower.algebraMap_apply ℂ P J,
    lpsOriginalJFractionEmbedding_polynomial]
  simp only [lpsOriginalJHolomorphicEval, Polynomial.algebraMap_eq, Polynomial.aeval_C]
  exact (IsScalarTower.algebraMap_apply ℂ LPSOriginalHolomorphicRing
    LPSOriginalHolomorphicFractionField c).symm
variable [NeZero N]
lemma lpsOriginalGenericPolynomial_formallyEtale : Algebra.FormallyEtale P K := by
  let : FiniteDimensional J K := lpsOriginalGeneratedFunctionField_finiteDimensional N hpos
  let : Algebra.IsSeparable J K := inferInstance
  let : Algebra.FormallyEtale J K := Algebra.FormallyEtale.of_isSeparable J K
  let : Algebra.FormallyEtale P J :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  exact Algebra.FormallyEtale.comp P J K
def lpsOriginalGenericKaehlerCoefficientEquiv : KaehlerDifferential ℂ K ≃ₗ[K] K := by
  let : Algebra.FormallyEtale P K := lpsOriginalGenericPolynomial_formallyEtale N hpos
  exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ P K).symm |>.trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
      (KaehlerDifferential.polynomialEquiv ℂ)).trans
        (TensorProduct.AlgebraTensorModule.rid P K K))
end GenericDifferential
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane TensorProduct
noncomputable section
section GenericMeromorphicDifferential
variable (N : ℕ) (hpos : 0 < N)
local instance _p2m_local_instance_6f8db27f7a_135 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance _p2m_local_instance_6f8db27f7a_141 : Algebra P K :=
  ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance _p2m_local_instance_6f8db27f7a_143 : Algebra ℂ K :=
  ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance _p2m_local_instance_6f8db27f7a_145 : IsScalarTower P J K := IsScalarTower.of_algebraMap_eq' rfl
local instance _p2m_local_instance_6f8db27f7a_146 : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local instance _p2m_local_instance_6f8db27f7a_147 : IsScalarTower ℂ P K := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap J K (algebraMap ℂ J c) =
    algebraMap J K (algebraMap P J (algebraMap ℂ P c))
  rw [IsScalarTower.algebraMap_apply ℂ P J]
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet
def lpsOriginalGenericToMeromorphicGerm : K →ₐ[ℂ] M where
  toRingHom := lpsOriginalHolomorphicFractionToMeromorphicGerm.comp
    (lpsOriginalGeneratedFunctionField N hpos).val.toRingHom
  commutes' c := by
    change lpsOriginalHolomorphicFractionToMeromorphicGerm
      (algebraMap ℂ K c).val = algebraMap ℂ M c
    rw [lpsOriginalGenericComplexConstant_value,IsScalarTower.algebraMap_apply ℂ
      LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField,
      lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic,
      lpsOriginalHolomorphicToMeromorphicGerm_constant]
local instance _p2m_local_instance_6f8db27f7a_178 : Algebra K M := (lpsOriginalGenericToMeromorphicGerm N hpos).toAlgebra
def lpsOriginalGenericMeromorphicDerivation : Derivation ℂ K M := by
  let φ := lpsOriginalGenericToMeromorphicGerm N hpos
  let D : K →ₗ[ℂ] M :=
    { toFun := fun f => lpsOriginalMeromorphicGermCoefficientDerivative
        UpperHalfPlane.upperHalfPlaneSet (φ f)
      map_add' := by
        intro f g
        rw [map_add,lpsOriginalMeromorphicGermCoefficientDerivative_add]
      map_smul' := by
        intro c f
        rw [map_smul]
        change lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
          (lpsOriginalMeromorphicGermComplexConstants UpperHalfPlane.upperHalfPlaneSet c * φ f) =
            lpsOriginalMeromorphicGermComplexConstants UpperHalfPlane.upperHalfPlaneSet c *
              lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet (φ f)
        rw [lpsOriginalMeromorphicGermCoefficientDerivative_mul,
          lpsOriginalMeromorphicGermCoefficientDerivative_constant,mul_zero,add_zero] }
  refine Derivation.mk' D ?_
  intro f g
  change lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
    (φ (f*g)) = φ f * lpsOriginalMeromorphicGermCoefficientDerivative
      UpperHalfPlane.upperHalfPlaneSet (φ g) + φ g *
        lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet (φ f)
  rw [map_mul,lpsOriginalMeromorphicGermCoefficientDerivative_mul]
def lpsOriginalGenericMeromorphicDifferentialMap : KaehlerDifferential ℂ K →ₗ[K] M :=
  (lpsOriginalGenericMeromorphicDerivation N hpos).liftKaehlerDifferential
variable [NeZero N]
def lpsOriginalGenericJDerivation : Derivation ℂ K K :=
  (lpsOriginalGenericKaehlerCoefficientEquiv N hpos).compDer (KaehlerDifferential.D ℂ K)
def lpsOriginalGenericMeromorphicDifferentialTensorEquiv :
    M ⊗[K] KaehlerDifferential ℂ K ≃ₗ[M] M :=
  ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl M M)
    (lpsOriginalGenericKaehlerCoefficientEquiv N hpos)).trans
      (TensorProduct.AlgebraTensorModule.rid K M M)).trans
        (LinearEquiv.smulOfNeZero M M
          (lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
            (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic))
          lpsOriginalJMeromorphicDerivative_ne_zero)
end GenericMeromorphicDifferential
end
end QEC.Coding.TannerLiftedProduct


