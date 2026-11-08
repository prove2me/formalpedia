-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRegularDifferentialFiniteness
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRegularDifferentialFiniteness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:08:15.29053+00:00
-- url     : https://prove2.me/theorems/db8988b8-284a-4bbe-b2fc-ad02dded9feb
-- title:
--   LPSOriginal Regular Differential Finiteness
-- statement:
--   Definitions and structural lemmas for LPSOriginal Regular Differential Finiteness, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRegularDifferentialFiniteness.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroDifferentialLattice
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInverseDifferentialLattice
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRatFuncConstantTower
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRatFuncFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRatFuncPolynomialTower
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
open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance]
  LPSOriginalLocalKaehlerFinitenessDictionary001
  LPSOriginalLocalKaehlerFinitenessDictionary002
  LPSOriginalLocalKaehlerFinitenessDictionary003
  LPSOriginalLocalKaehlerFinitenessDictionary004
  LPSOriginalLocalKaehlerFinitenessDictionary005
  LPSOriginalLocalKaehlerFinitenessDictionary006
  LPSOriginalLocalKaehlerFinitenessDictionary007
  LPSOriginalLocalKaehlerFinitenessDictionary008
  LPSOriginalLocalKaehlerFinitenessDictionary009
  LPSOriginalLocalKaehlerFinitenessDictionary010
  LPSOriginalLocalKaehlerFinitenessDictionary011
  LPSOriginalLocalKaehlerFinitenessDictionary012
  LPSOriginalLocalKaehlerFinitenessDictionary013
  LPSOriginalLocalKaehlerFinitenessDictionary014
  LPSOriginalLocalKaehlerFinitenessDictionary015
  LPSOriginalLocalKaehlerFinitenessDictionary016
  LPSOriginalLocalKaehlerFinitenessDictionary017
  LPSOriginalLocalKaehlerFinitenessDictionary018
  LPSOriginalLocalKaehlerFinitenessDictionary031
  LPSOriginalLocalKaehlerFinitenessDictionary032
  LPSOriginalLocalKaehlerFinitenessDictionary033
  LPSOriginalLocalKaehlerFinitenessDictionary034
  LPSOriginalLocalKaehlerFinitenessDictionary035
  LPSOriginalLocalKaehlerFinitenessDictionary036
  LPSOriginalLocalKaehlerFinitenessDictionary037
  LPSOriginalLocalKaehlerFinitenessDictionary038
  LPSOriginalLocalKaehlerFinitenessDictionary039
  LPSOriginalLocalKaehlerFinitenessDictionary040
  LPSOriginalLocalKaehlerFinitenessDictionary041
  LPSOriginalLocalKaehlerFinitenessDictionary042
local instance _p2m_local_instance_d13105efee_58 : Algebra (RatFunc ℂ) K := lpsOriginalRatFuncAlgebra N hpos
local instance _p2m_local_instance_d13105efee_59 : IsScalarTower P (RatFunc ℂ) K := lpsOriginalRatFuncPolynomialTower N hpos
local instance _p2m_local_instance_d13105efee_60 : IsScalarTower ℂ (RatFunc ℂ) K := lpsOriginalRatFuncConstantTower N hpos
local instance _p2m_local_instance_d13105efee_61 : _root_.FunctionField ℂ K := lpsOriginalRatFuncFunctionField N hpos
local instance _p2m_local_instance_d13105efee_63 : SMulCommClass ℂ K K where
  smul_comm c f g := by simp only [Algebra.smul_def]; ring
local instance _p2m_local_instance_d13105efee_65 : SMul K (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_d13105efee_67 : Module K (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_d13105efee_70 : Algebra P I := lpsOriginalInfinityPolynomialAlgebra N hpos
local instance _p2m_local_instance_d13105efee_71 : SMulCommClass ℂ P I where
  smul_comm c p r := by simp only [Algebra.smul_def]; ring
local instance _p2m_local_instance_d13105efee_73 : SMul P (KaehlerDifferential ℂ I) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ I
local instance _p2m_local_instance_d13105efee_75 : Module P (KaehlerDifferential ℂ I) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ I
def lpsOriginalRegularCoefficientMap :
    lpsOriginalNativeRegularKaehlerSubmodule N hpos →ₗ[ℂ] K :=
  ((lpsOriginalGenericKaehlerCoefficientEquiv N hpos).restrictScalars ℂ).toLinearMap.comp
    (lpsOriginalNativeRegularKaehlerSubmodule N hpos).subtype
def lpsOriginalRegularCoefficientSubmodule : Submodule ℂ K :=
  (lpsOriginalRegularCoefficientMap N hpos).range
end
end QEC.Coding.TannerLiftedProduct


