-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerCompatibility
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerCompatibility
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:23:55.394402+00:00
-- url     : https://prove2.me/theorems/47b4f093-5f4c-4c88-b1c3-8caab02a0d03
-- title:
--   LPSOriginal Affine Kaehler Compatibility
-- statement:
--   Definitions and structural lemmas for LPSOriginal Affine Kaehler Compatibility, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalAffineKaehlerCompatibility.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerInjective
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalTwoChartDifferentials
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
local instance LPSOriginalAffineKaehlerCompatibilityDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local instance LPSOriginalAffineKaehlerCompatibilityDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalAffineKaehlerCompatibilityDictionary005 : Algebra ℂ R := (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary006 : SMul ℂ R := Algebra.toSMul
local instance LPSOriginalAffineKaehlerCompatibilityDictionary007 : Module ℂ R := Algebra.toModule
local instance LPSOriginalAffineKaehlerCompatibilityDictionary008 : SMulCommClass ℂ R R where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary009 : SMul R (KaehlerDifferential ℂ R) := instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalAffineKaehlerCompatibilityDictionary010 : Module R (KaehlerDifferential ℂ R) := instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance LPSOriginalAffineKaehlerCompatibilityDictionary011 : IsScalarTower ℂ R K := .of_algebraMap_eq fun c =>
  (lpsOriginalZeroConstant_value N hpos c).symm
local instance LPSOriginalAffineKaehlerCompatibilityDictionary012 : SMulCommClass ℂ R K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary013 : SMul R (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerCompatibilityDictionary014 : Module R (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerCompatibilityDictionary015 : IsDedekindDomain R := lpsOriginalZeroChart_isDedekindDomain N hpos
local instance LPSOriginalAffineKaehlerCompatibilityDictionary016 : IsFractionRing R K := lpsOriginalZeroChart_isFractionRing N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local instance LPSOriginalAffineKaehlerCompatibilityDictionary017 : Algebra ℂ I := (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary018 : SMul ℂ I := Algebra.toSMul
local instance LPSOriginalAffineKaehlerCompatibilityDictionary019 : Module ℂ I := Algebra.toModule
local instance LPSOriginalAffineKaehlerCompatibilityDictionary020 : SMulCommClass ℂ I I where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary021 : SMul I (KaehlerDifferential ℂ I) := instSMulKaehlerDifferentialOfSMulCommClass ℂ I
local instance LPSOriginalAffineKaehlerCompatibilityDictionary022 : Module I (KaehlerDifferential ℂ I) := instModuleKaehlerDifferentialOfSMulCommClass ℂ I
local instance LPSOriginalAffineKaehlerCompatibilityDictionary023 : IsScalarTower ℂ I K := .of_algebraMap_eq fun c =>
  (lpsOriginalInfinityConstant_value N hpos c).symm
local instance LPSOriginalAffineKaehlerCompatibilityDictionary024 : SMulCommClass ℂ I K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary025 : SMul I (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerCompatibilityDictionary026 : Module I (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local notation "L" => LaurentPolynomial ℂ
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
local instance LPSOriginalAffineKaehlerCompatibilityDictionary027 : Algebra L K := (lpsOriginalComplexLaurentBaseToGeneratedField N hpos).toAlgebra
lemma lpsOriginalLaurentConstant_value (c : ℂ) :
    (lpsOriginalComplexLaurentConstantRingHom N hpos c).val = algebraMap ℂ K c := by
  have hc := congrArg (fun t : T => t.val)
    (RingHom.congr_fun (lpsOriginalComplexZeroConstantOverlapRingHomDiagram N hpos) c)
  change (lpsOriginalComplexZeroConstantRingHom N hpos c).val =
    (lpsOriginalComplexLaurentConstantRingHom N hpos c).val at hc
  exact hc.symm.trans (lpsOriginalZeroConstant_value N hpos c)
local instance LPSOriginalAffineKaehlerCompatibilityDictionary028 : Algebra ℂ T := (lpsOriginalComplexLaurentConstantRingHom N hpos).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary029 : SMul ℂ T := Algebra.toSMul
local instance LPSOriginalAffineKaehlerCompatibilityDictionary030 : Module ℂ T := Algebra.toModule
local instance LPSOriginalAffineKaehlerCompatibilityDictionary031 : SMulCommClass ℂ T T where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary032 : SMul T (KaehlerDifferential ℂ T) := instSMulKaehlerDifferentialOfSMulCommClass ℂ T
local instance LPSOriginalAffineKaehlerCompatibilityDictionary033 : Module T (KaehlerDifferential ℂ T) := instModuleKaehlerDifferentialOfSMulCommClass ℂ T
local instance LPSOriginalAffineKaehlerCompatibilityDictionary034 : IsScalarTower ℂ T K := .of_algebraMap_eq fun c =>
  (lpsOriginalLaurentConstant_value N hpos c).symm
local instance LPSOriginalAffineKaehlerCompatibilityDictionary035 : SMulCommClass ℂ T K where
  smul_comm c r k := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary036 : SMul T (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerCompatibilityDictionary037 : Module T (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalAffineKaehlerCompatibilityDictionary038 : Algebra R T := (lpsOriginalComplexNormalZeroToLaurent N hpos).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary039 : SMul R T := Algebra.toSMul
local instance LPSOriginalAffineKaehlerCompatibilityDictionary040 : Module R T := Algebra.toModule
local instance LPSOriginalAffineKaehlerCompatibilityDictionary041 : IsScalarTower R T K := .of_algebraMap_eq fun r => by rfl
local instance LPSOriginalAffineKaehlerCompatibilityDictionary042 : IsScalarTower ℂ R T := .of_algebraMap_eq fun c =>
  (RingHom.congr_fun (lpsOriginalComplexZeroConstantOverlapRingHomDiagram N hpos) c).symm
local instance LPSOriginalAffineKaehlerCompatibilityDictionary043 : SMulCommClass ℂ R T where
  smul_comm c r t := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary044 : SMul R (KaehlerDifferential ℂ T) := instSMulKaehlerDifferentialOfSMulCommClass ℂ T
local instance LPSOriginalAffineKaehlerCompatibilityDictionary045 : Module R (KaehlerDifferential ℂ T) := instModuleKaehlerDifferentialOfSMulCommClass ℂ T
local instance LPSOriginalAffineKaehlerCompatibilityDictionary046 : IsLocalization.Away (algebraMap P R Polynomial.X) T :=
  lpsOriginalComplexNormalLaurent_localization N hpos
local instance LPSOriginalAffineKaehlerCompatibilityDictionary047 : Algebra I T := (lpsOriginalComplexNormalInfinityToLaurent N hpos).toAlgebra
local instance LPSOriginalAffineKaehlerCompatibilityDictionary048 : SMul I T := Algebra.toSMul
local instance LPSOriginalAffineKaehlerCompatibilityDictionary049 : Module I T := Algebra.toModule
local instance LPSOriginalAffineKaehlerCompatibilityDictionary050 : IsScalarTower I T K := .of_algebraMap_eq fun r => by rfl
local instance LPSOriginalAffineKaehlerCompatibilityDictionary051 : IsScalarTower ℂ I T := .of_algebraMap_eq fun c =>
  (RingHom.congr_fun (lpsOriginalComplexInfinityConstantOverlapRingHomDiagram N hpos) c).symm
local instance LPSOriginalAffineKaehlerCompatibilityDictionary052 : SMulCommClass ℂ I T where
  smul_comm c r t := by simp only [Algebra.smul_def]; ring
local instance LPSOriginalAffineKaehlerCompatibilityDictionary053 : SMul I (KaehlerDifferential ℂ T) := instSMulKaehlerDifferentialOfSMulCommClass ℂ T
local instance LPSOriginalAffineKaehlerCompatibilityDictionary054 : Module I (KaehlerDifferential ℂ T) := instModuleKaehlerDifferentialOfSMulCommClass ℂ T
end
end QEC.Coding.TannerLiftedProduct


