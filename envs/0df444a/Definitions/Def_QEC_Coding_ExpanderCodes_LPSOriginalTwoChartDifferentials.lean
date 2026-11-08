-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalTwoChartDifferentials
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalTwoChartDifferentials
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:06:15.99538+00:00
-- url     : https://prove2.me/theorems/cc49a747-7ad8-4e4a-97a9-d0ec6bfdcbe2
-- title:
--   LPSOriginal Two Chart Differentials
-- statement:
--   Definitions and structural lemmas for LPSOriginal Two Chart Differentials, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalTwoChartDifferentials.lean

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
local instance LPSOriginalTwoChartDifferentialsDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local instance LPSOriginalTwoChartDifferentialsDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalTwoChartDifferentialsDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalTwoChartDifferentialsDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalTwoChartDifferentialsDictionary005 : Algebra ℂ R := (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
local instance LPSOriginalTwoChartDifferentialsDictionary006 : SMul ℂ R := Algebra.toSMul
local instance LPSOriginalTwoChartDifferentialsDictionary007 : Module ℂ R := Algebra.toModule
local instance LPSOriginalTwoChartDifferentialsDictionary008 : SMulCommClass ℂ R R where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalTwoChartDifferentialsDictionary009 : SMul R (KaehlerDifferential ℂ R) := instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalTwoChartDifferentialsDictionary010 : Module R (KaehlerDifferential ℂ R) := instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalTwoChartDifferentialsDictionary011 : IsScalarTower ℂ R K := .of_algebraMap_eq fun c =>
  (lpsOriginalZeroConstant_value N hpos c).symm
local instance LPSOriginalTwoChartDifferentialsDictionary012 : SMulCommClass ℂ R K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalTwoChartDifferentialsDictionary013 : SMul R (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalTwoChartDifferentialsDictionary014 : Module R (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalTwoChartDifferentialsDictionary015 : IsDedekindDomain R := lpsOriginalZeroChart_isDedekindDomain N hpos
local instance LPSOriginalTwoChartDifferentialsDictionary016 : IsFractionRing R K := lpsOriginalZeroChart_isFractionRing N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local instance LPSOriginalTwoChartDifferentialsDictionary017 : Algebra ℂ I := (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
local instance LPSOriginalTwoChartDifferentialsDictionary018 : SMul ℂ I := Algebra.toSMul
local instance LPSOriginalTwoChartDifferentialsDictionary019 : Module ℂ I := Algebra.toModule
local instance LPSOriginalTwoChartDifferentialsDictionary020 : SMulCommClass ℂ I I where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalTwoChartDifferentialsDictionary021 : SMul I (KaehlerDifferential ℂ I) := instSMulKaehlerDifferentialOfSMulCommClass ℂ I
local instance LPSOriginalTwoChartDifferentialsDictionary022 : Module I (KaehlerDifferential ℂ I) := instModuleKaehlerDifferentialOfSMulCommClass ℂ I
local instance LPSOriginalTwoChartDifferentialsDictionary023 : IsScalarTower ℂ I K := .of_algebraMap_eq fun c =>
  (lpsOriginalInfinityConstant_value N hpos c).symm
local instance LPSOriginalTwoChartDifferentialsDictionary024 : SMulCommClass ℂ I K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalTwoChartDifferentialsDictionary025 : SMul I (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalTwoChartDifferentialsDictionary026 : Module I (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
end
end QEC.Coding.TannerLiftedProduct


