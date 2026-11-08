-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialRestriction
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalDifferentialRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:31:06.546057+00:00
-- url     : https://prove2.me/theorems/c0f48e07-e701-423d-8dec-616cc603593e
-- title:
--   LPSOriginal Differential Restriction
-- statement:
--   Definitions and structural lemmas for LPSOriginal Differential Restriction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialRestriction.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGlobalConstantMap_infinity_affine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGlobalConstantMap_zero_affine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGluedChartMap_openImmersion

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "Z" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "c" => lpsOriginalComplexNormalGlobalConstantMap N hpos
local instance lpsOriginalChartDifferentialRestrictionOpenImmersion (b : Bool) :
    IsOpenImmersion (lpsOriginalComplexNormalGluedChartMap N hpos b) :=
  lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos b
attribute [local instance] lpsOriginalZeroChartDifferentialAlgebra
  lpsOriginalInfinityChartDifferentialAlgebra lpsOriginalZeroChartDifferentialSMul
  lpsOriginalZeroChartDifferentialModule lpsOriginalZeroChartDifferentialSMulComm
  lpsOriginalZeroChartOmegaSMul lpsOriginalZeroChartOmegaModule
  lpsOriginalInfinityChartDifferentialSMul lpsOriginalInfinityChartDifferentialModule
  lpsOriginalInfinityChartDifferentialSMulComm lpsOriginalInfinityChartOmegaSMul
  lpsOriginalInfinityChartOmegaModule
def lpsOriginalComplexNormalChartDifferentialRestrictionIso (b : Bool) :
    schemeDifferentialSheaf (lpsOriginalComplexNormalSchemeChart N hpos b) (CommRingCat.of ℂ)
      (c ≫ (lpsOriginalComplexNormalGluedChartMap N hpos b).appTop) ≅
    (Scheme.Modules.restrictFunctor (lpsOriginalComplexNormalGluedChartMap N hpos b)).obj
      (lpsOriginalComplexNormalDifferentialSheaf N hpos) :=
  schemeDifferentialRestrictionIso (lpsOriginalComplexNormalGluedChartMap N hpos b)
    (CommRingCat.of ℂ) c
def lpsOriginalZeroChartGlobalDifferentialRestrictionIso :
    (Scheme.Modules.restrictFunctor (lpsOriginalComplexNormalGluedChartMap N hpos false)).obj
      (lpsOriginalComplexNormalDifferentialSheaf N hpos) ≅
    tilde (R := CommRingCat.of Z) (ModuleCat.of Z (KaehlerDifferential ℂ Z)) := by
  have h : (c ≫ (lpsOriginalComplexNormalGluedChartMap N hpos false).appTop :
      CommRingCat.of ℂ ⟶ Γ(Spec (CommRingCat.of Z), ⊤)) =
      affineDifferentialGlobalConstantMap ℂ (CommRingCat.of Z) :=
    lpsOriginalComplexNormalGlobalConstantMap_zero_affine N hpos
  exact (lpsOriginalComplexNormalChartDifferentialRestrictionIso N hpos false).symm ≪≫
    eqToIso (congrArg (fun c' : CommRingCat.of ℂ ⟶ Γ(Spec (CommRingCat.of Z), ⊤) =>
      schemeDifferentialSheaf (Spec (CommRingCat.of Z)) (CommRingCat.of ℂ) c') h) ≪≫
    lpsOriginalZeroChartDifferentialSheafIso N hpos
def lpsOriginalInfinityChartGlobalDifferentialRestrictionIso :
    (Scheme.Modules.restrictFunctor (lpsOriginalComplexNormalGluedChartMap N hpos true)).obj
      (lpsOriginalComplexNormalDifferentialSheaf N hpos) ≅
    tilde (R := CommRingCat.of I) (ModuleCat.of I (KaehlerDifferential ℂ I)) := by
  have h : (c ≫ (lpsOriginalComplexNormalGluedChartMap N hpos true).appTop :
      CommRingCat.of ℂ ⟶ Γ(Spec (CommRingCat.of I), ⊤)) =
      affineDifferentialGlobalConstantMap ℂ (CommRingCat.of I) :=
    lpsOriginalComplexNormalGlobalConstantMap_infinity_affine N hpos
  exact (lpsOriginalComplexNormalChartDifferentialRestrictionIso N hpos true).symm ≪≫
    eqToIso (congrArg (fun c' : CommRingCat.of ℂ ⟶ Γ(Spec (CommRingCat.of I), ⊤) =>
      schemeDifferentialSheaf (Spec (CommRingCat.of I)) (CommRingCat.of ℂ) c') h) ≪≫
    lpsOriginalInfinityChartDifferentialSheafIso N hpos
end
end QEC.Coding.TannerLiftedProduct


