-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T06:53:39.661862+00:00
-- url     : https://prove2.me/theorems/c56100ac-fa14-449e-9065-7775bf11b83b
-- title:
--   LPSOriginal Differential Sheaf
-- statement:
--   Definitions and structural lemmas for LPSOriginal Differential Sheaf, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialSheaf.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
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
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
def lpsOriginalComplexNormalGlobalConstantMap : CommRingCat.of ℂ ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
    (lpsOriginalComplexNormalGluedToSpecC N hpos).appTop
def lpsOriginalComplexNormalDifferentialSheaf : Scheme.Modules X :=
  schemeDifferentialSheaf X (CommRingCat.of ℂ)
    (lpsOriginalComplexNormalGlobalConstantMap N hpos)
def lpsOriginalComplexNormalDifferentialSheafDerivation :
    ((Scheme.Modules.toPresheafOfModules X).obj
      (lpsOriginalComplexNormalDifferentialSheaf N hpos)).Derivation'
        (schemeConstantPresheafMap X (CommRingCat.of ℂ)
          (lpsOriginalComplexNormalGlobalConstantMap N hpos)) :=
  schemeDifferentialSheafDerivation X (CommRingCat.of ℂ)
    (lpsOriginalComplexNormalGlobalConstantMap N hpos)
local notation "Z" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local instance lpsOriginalZeroChartDifferentialAlgebra : Algebra ℂ Z :=
  (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
local instance lpsOriginalInfinityChartDifferentialAlgebra : Algebra ℂ I :=
  (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
local instance lpsOriginalZeroChartDifferentialSMul : SMul ℂ Z := Algebra.toSMul
local instance lpsOriginalZeroChartDifferentialModule : Module ℂ Z := Algebra.toModule
local instance lpsOriginalZeroChartDifferentialSMulComm : SMulCommClass ℂ Z Z where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance lpsOriginalZeroChartOmegaSMul : SMul Z (KaehlerDifferential ℂ Z) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ Z
local instance lpsOriginalZeroChartOmegaModule : Module Z (KaehlerDifferential ℂ Z) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ Z
local instance lpsOriginalInfinityChartDifferentialSMul : SMul ℂ I := Algebra.toSMul
local instance lpsOriginalInfinityChartDifferentialModule : Module ℂ I := Algebra.toModule
local instance lpsOriginalInfinityChartDifferentialSMulComm : SMulCommClass ℂ I I where
  smul_comm c a b := by simp only [Algebra.smul_def]; ring
local instance lpsOriginalInfinityChartOmegaSMul : SMul I (KaehlerDifferential ℂ I) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ I
local instance lpsOriginalInfinityChartOmegaModule : Module I (KaehlerDifferential ℂ I) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ I
def lpsOriginalZeroChartDifferentialSheafIso :
    schemeDifferentialSheaf (Spec (CommRingCat.of Z)) (CommRingCat.of ℂ)
      (affineDifferentialGlobalConstantMap ℂ (CommRingCat.of Z)) ≅
    tilde (R := CommRingCat.of Z) (ModuleCat.of Z (KaehlerDifferential ℂ Z)) :=
  affineDifferentialSheafIso ℂ (CommRingCat.of Z)
def lpsOriginalInfinityChartDifferentialSheafIso :
    schemeDifferentialSheaf (Spec (CommRingCat.of I)) (CommRingCat.of ℂ)
      (affineDifferentialGlobalConstantMap ℂ (CommRingCat.of I)) ≅
    tilde (R := CommRingCat.of I) (ModuleCat.of I (KaehlerDifferential ℂ I)) :=
  affineDifferentialSheafIso ℂ (CommRingCat.of I)
end
end QEC.Coding.TannerLiftedProduct


