-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerFiniteness
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerFiniteness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:05:43.32475+00:00
-- url     : https://prove2.me/theorems/c6f6e925-ae44-46c0-87c4-f0089095000a
-- title:
--   LPSOriginal Local Kaehler Finiteness
-- statement:
--   Definitions and structural lemmas for LPSOriginal Local Kaehler Finiteness, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalKaehlerFiniteness.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityAffineDifferentials
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finiteDimensional
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
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalLocalKaehlerFinitenessDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local instance LPSOriginalLocalKaehlerFinitenessDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalLocalKaehlerFinitenessDictionary005 : Algebra ℂ R := (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary006 : SMul ℂ R := Algebra.toSMul
local instance LPSOriginalLocalKaehlerFinitenessDictionary007 : Module ℂ R := Algebra.toModule
local instance LPSOriginalLocalKaehlerFinitenessDictionary008 : SMulCommClass ℂ R R where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalLocalKaehlerFinitenessDictionary009 : SMul R (KaehlerDifferential ℂ R) := instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalLocalKaehlerFinitenessDictionary010 : Module R (KaehlerDifferential ℂ R) := instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalLocalKaehlerFinitenessDictionary011 : IsScalarTower ℂ R K := .of_algebraMap_eq fun c =>
  (lpsOriginalZeroConstant_value N hpos c).symm
local instance LPSOriginalLocalKaehlerFinitenessDictionary012 : SMulCommClass ℂ R K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalLocalKaehlerFinitenessDictionary013 : SMul R (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary014 : Module R (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary015 : IsDedekindDomain R := lpsOriginalZeroChart_isDedekindDomain N hpos
local instance LPSOriginalLocalKaehlerFinitenessDictionary016 : IsFractionRing R K := lpsOriginalZeroChart_isFractionRing N hpos
local instance LPSOriginalLocalKaehlerFinitenessDictionary017 : IsScalarTower P J K := .of_algebraMap_eq' rfl
local instance LPSOriginalLocalKaehlerFinitenessDictionary018 : FiniteDimensional J K := lpsOriginalGeneratedFunctionField_finiteDimensional N hpos
section localPoint
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance LPSOriginalLocalKaehlerFinitenessDictionary019 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary020 : SMul V K := Algebra.toSMul
local instance LPSOriginalLocalKaehlerFinitenessDictionary021 : Module V K := Algebra.toModule
local instance LPSOriginalLocalKaehlerFinitenessDictionary022 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance LPSOriginalLocalKaehlerFinitenessDictionary023 : SMul V (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary024 : Module V (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary025 : Algebra ℂ V :=
  (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary026 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl
end localPoint
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalLocalKaehlerFinitenessDictionary027 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
local instance LPSOriginalLocalKaehlerFinitenessDictionary028 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary029 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary030 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalLocalKaehlerFinitenessDictionary031 : Algebra ℂ R := (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary032 : SMul ℂ R := Algebra.toSMul
local instance LPSOriginalLocalKaehlerFinitenessDictionary033 : Module ℂ R := Algebra.toModule
local instance LPSOriginalLocalKaehlerFinitenessDictionary034 : SMulCommClass ℂ R R where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalLocalKaehlerFinitenessDictionary035 : SMul R (KaehlerDifferential ℂ R) := instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalLocalKaehlerFinitenessDictionary036 : Module R (KaehlerDifferential ℂ R) := instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalLocalKaehlerFinitenessDictionary037 : IsScalarTower ℂ R K := .of_algebraMap_eq fun c =>
  (lpsOriginalInfinityConstant_value N hpos c).symm
local instance LPSOriginalLocalKaehlerFinitenessDictionary038 : SMulCommClass ℂ R K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalLocalKaehlerFinitenessDictionary039 : SMul R (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary040 : Module R (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary041 : IsDedekindDomain R := lpsOriginalInfinityChart_isDedekindDomain N hpos
local instance LPSOriginalLocalKaehlerFinitenessDictionary042 : IsFractionRing R K := lpsOriginalInfinityChart_isFractionRing N hpos
local instance LPSOriginalLocalKaehlerFinitenessDictionary043 : FiniteDimensional J K := lpsOriginalGeneratedFunctionField_finiteDimensional N hpos
section localPoint
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance LPSOriginalLocalKaehlerFinitenessDictionary044 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary045 : SMul V K := Algebra.toSMul
local instance LPSOriginalLocalKaehlerFinitenessDictionary046 : Module V K := Algebra.toModule
local instance LPSOriginalLocalKaehlerFinitenessDictionary047 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance LPSOriginalLocalKaehlerFinitenessDictionary048 : SMul V (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary049 : Module V (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerFinitenessDictionary050 : Algebra ℂ V :=
  (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance LPSOriginalLocalKaehlerFinitenessDictionary051 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl
end localPoint
end
end QEC.Coding.TannerLiftedProduct


