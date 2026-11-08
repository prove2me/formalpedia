-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeGlobalDifferentials
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNativeGlobalDifferentials
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:36:14.387178+00:00
-- url     : https://prove2.me/theorems/37c34f38-f0ab-4739-870f-409807c2722c
-- title:
--   LPSOriginal Native Global Differentials
-- statement:
--   Definitions and structural lemmas for LPSOriginal Native Global Differentials, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeGlobalDifferentials.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineChartDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialImages
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerCompatibility
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGlobalConstantMap_infinity_affine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGlobalConstantMap_zero_affine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGluedChartMap_openImmersion

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
attribute [local instance] lpsOriginalZeroChartDifferentialAlgebra
  lpsOriginalInfinityChartDifferentialAlgebra lpsOriginalZeroChartDifferentialSMul
  lpsOriginalZeroChartDifferentialModule lpsOriginalZeroChartDifferentialSMulComm
  lpsOriginalZeroChartOmegaSMul lpsOriginalZeroChartOmegaModule
  lpsOriginalInfinityChartDifferentialSMul lpsOriginalInfinityChartDifferentialModule
  lpsOriginalInfinityChartDifferentialSMulComm lpsOriginalInfinityChartOmegaSMul
  lpsOriginalInfinityChartOmegaModule
  LPSOriginalAffineKaehlerCompatibilityDictionary028
  LPSOriginalAffineKaehlerCompatibilityDictionary029
  LPSOriginalAffineKaehlerCompatibilityDictionary030
  LPSOriginalAffineKaehlerCompatibilityDictionary031
  LPSOriginalAffineKaehlerCompatibilityDictionary032
  LPSOriginalAffineKaehlerCompatibilityDictionary033
  LPSOriginalAffineKaehlerCompatibilityDictionary038
  LPSOriginalAffineKaehlerCompatibilityDictionary039
  LPSOriginalAffineKaehlerCompatibilityDictionary040
  LPSOriginalAffineKaehlerCompatibilityDictionary042
  LPSOriginalAffineKaehlerCompatibilityDictionary043
  LPSOriginalAffineKaehlerCompatibilityDictionary044
  LPSOriginalAffineKaehlerCompatibilityDictionary045
  LPSOriginalAffineKaehlerCompatibilityDictionary047
  LPSOriginalAffineKaehlerCompatibilityDictionary048
  LPSOriginalAffineKaehlerCompatibilityDictionary049
  LPSOriginalAffineKaehlerCompatibilityDictionary051
  LPSOriginalAffineKaehlerCompatibilityDictionary052
  LPSOriginalAffineKaehlerCompatibilityDictionary053
  LPSOriginalAffineKaehlerCompatibilityDictionary054
local instance originalZeroLaurentRestrictionOpen :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (lpsOriginalComplexNormalZeroToLaurent N hpos))) :=
  lpsOriginalComplexNormalZeroToLaurent_openImmersion N hpos
local instance originalInfinityLaurentRestrictionOpen :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (lpsOriginalComplexNormalInfinityToLaurent N hpos))) :=
  lpsOriginalComplexNormalInfinityToLaurent_openImmersion N hpos
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "c" => lpsOriginalComplexNormalGlobalConstantMap N hpos
local notation "Omega" => lpsOriginalComplexNormalDifferentialSheaf N hpos
local notation "f0" => lpsOriginalComplexNormalGluedChartMap N hpos false
local notation "f1" => lpsOriginalComplexNormalGluedChartMap N hpos true
local notation "q0" => CommRingCat.ofHom (lpsOriginalComplexNormalZeroToLaurent N hpos)
local notation "q1" => CommRingCat.ofHom (lpsOriginalComplexNormalInfinityToLaurent N hpos)
attribute [local instance] lpsOriginalZeroChartDifferentialAlgebra
  lpsOriginalInfinityChartDifferentialAlgebra lpsOriginalZeroChartDifferentialSMul
  lpsOriginalZeroChartDifferentialModule lpsOriginalZeroChartDifferentialSMulComm
  lpsOriginalZeroChartOmegaSMul lpsOriginalZeroChartOmegaModule
  lpsOriginalInfinityChartDifferentialSMul lpsOriginalInfinityChartDifferentialModule
  lpsOriginalInfinityChartDifferentialSMulComm lpsOriginalInfinityChartOmegaSMul
  lpsOriginalInfinityChartOmegaModule
  LPSOriginalAffineKaehlerCompatibilityDictionary028
  LPSOriginalAffineKaehlerCompatibilityDictionary029
  LPSOriginalAffineKaehlerCompatibilityDictionary030
  LPSOriginalAffineKaehlerCompatibilityDictionary031
  LPSOriginalAffineKaehlerCompatibilityDictionary032
  LPSOriginalAffineKaehlerCompatibilityDictionary033
  LPSOriginalAffineKaehlerCompatibilityDictionary038
  LPSOriginalAffineKaehlerCompatibilityDictionary039
  LPSOriginalAffineKaehlerCompatibilityDictionary040
  LPSOriginalAffineKaehlerCompatibilityDictionary042
  LPSOriginalAffineKaehlerCompatibilityDictionary043
  LPSOriginalAffineKaehlerCompatibilityDictionary044
  LPSOriginalAffineKaehlerCompatibilityDictionary045
  LPSOriginalAffineKaehlerCompatibilityDictionary047
  LPSOriginalAffineKaehlerCompatibilityDictionary048
  LPSOriginalAffineKaehlerCompatibilityDictionary049
  LPSOriginalAffineKaehlerCompatibilityDictionary051
  LPSOriginalAffineKaehlerCompatibilityDictionary052
  LPSOriginalAffineKaehlerCompatibilityDictionary053
  LPSOriginalAffineKaehlerCompatibilityDictionary054
attribute [local instance] originalZeroLaurentRestrictionOpen originalInfinityLaurentRestrictionOpen
omit [NeZero N] in
local instance originalNativeGlobalZeroOpen :
    IsOpenImmersion (f0 : Spec (CommRingCat.of R) ⟶ X) :=
  lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos false
omit [NeZero N] in
local instance originalNativeGlobalInfinityOpen :
    IsOpenImmersion (f1 : Spec (CommRingCat.of I) ⟶ X) :=
  lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos true
omit [NeZero N] in
local instance originalNativeGlobalLaurentCompositeOpen :
    IsOpenImmersion (Spec.map (q0) ≫ (f0) : Spec (CommRingCat.of T) ⟶ X) :=
  @IsOpenImmersion.comp _ _ _ (Spec.map (q0)) (f0)
    (lpsOriginalComplexNormalZeroToLaurent_openImmersion N hpos)
    (originalNativeGlobalZeroOpen N hpos)
local notation "U" => Functor.obj (Scheme.Hom.opensFunctor (f0)) ⊤
local notation "V" => Functor.obj (Scheme.Hom.opensFunctor (f1)) ⊤
local notation "W" => Functor.obj (Scheme.Hom.opensFunctor (Spec.map (q0) ≫ (f0))) ⊤
def lpsOriginalZeroImageFromKaehler :
    AddCommGrpCat.of (KaehlerDifferential ℂ R) ≅ Γ(Omega, U) :=
  @affineDifferentialChartImageKaehlerIso ℂ (CommRingCat.of R) inferInstance inferInstance X
    (f0) (originalNativeGlobalZeroOpen N hpos) c
    (lpsOriginalComplexNormalGlobalConstantMap_zero_affine N hpos)
def lpsOriginalInfinityImageFromKaehler :
    AddCommGrpCat.of (KaehlerDifferential ℂ I) ≅ Γ(Omega, V) :=
  @affineDifferentialChartImageKaehlerIso ℂ (CommRingCat.of I) inferInstance inferInstance X
    (f1) (originalNativeGlobalInfinityOpen N hpos) c
    (lpsOriginalComplexNormalGlobalConstantMap_infinity_affine N hpos)
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
local notation "Omega" => lpsOriginalComplexNormalDifferentialSheaf N hpos
attribute [local instance] lpsOriginalZeroChartDifferentialAlgebra
  lpsOriginalInfinityChartDifferentialAlgebra lpsOriginalZeroChartDifferentialSMul
  lpsOriginalZeroChartDifferentialModule lpsOriginalZeroChartDifferentialSMulComm
  lpsOriginalZeroChartOmegaSMul lpsOriginalZeroChartOmegaModule
  lpsOriginalInfinityChartDifferentialSMul lpsOriginalInfinityChartDifferentialModule
  lpsOriginalInfinityChartDifferentialSMulComm lpsOriginalInfinityChartOmegaSMul
  lpsOriginalInfinityChartOmegaModule
  LPSOriginalAffineKaehlerCompatibilityDictionary028
  LPSOriginalAffineKaehlerCompatibilityDictionary029
  LPSOriginalAffineKaehlerCompatibilityDictionary030
  LPSOriginalAffineKaehlerCompatibilityDictionary031
  LPSOriginalAffineKaehlerCompatibilityDictionary032
  LPSOriginalAffineKaehlerCompatibilityDictionary033
  LPSOriginalAffineKaehlerCompatibilityDictionary038
  LPSOriginalAffineKaehlerCompatibilityDictionary039
  LPSOriginalAffineKaehlerCompatibilityDictionary040
  LPSOriginalAffineKaehlerCompatibilityDictionary042
  LPSOriginalAffineKaehlerCompatibilityDictionary043
  LPSOriginalAffineKaehlerCompatibilityDictionary044
  LPSOriginalAffineKaehlerCompatibilityDictionary045
  LPSOriginalAffineKaehlerCompatibilityDictionary047
  LPSOriginalAffineKaehlerCompatibilityDictionary048
  LPSOriginalAffineKaehlerCompatibilityDictionary049
  LPSOriginalAffineKaehlerCompatibilityDictionary051
  LPSOriginalAffineKaehlerCompatibilityDictionary052
  LPSOriginalAffineKaehlerCompatibilityDictionary053
  LPSOriginalAffineKaehlerCompatibilityDictionary054
attribute [local instance] originalNativeGlobalZeroOpen originalNativeGlobalInfinityOpen
local notation "U" => Functor.obj (Scheme.Hom.opensFunctor
  (lpsOriginalComplexNormalGluedChartMap N hpos false)) ⊤
local notation "V" => Functor.obj (Scheme.Hom.opensFunctor
  (lpsOriginalComplexNormalGluedChartMap N hpos true)) ⊤
def lpsOriginalNativeGlobalAffinePair :
    Γ(Omega, ⊤) → KaehlerDifferential ℂ R × KaehlerDifferential ℂ I :=
  schemeModuleGlobalIsoPair Omega U V
    (lpsOriginalZeroImageFromKaehler N hpos).symm
    (lpsOriginalInfinityImageFromKaehler N hpos).symm
end
end QEC.Coding.TannerLiftedProduct


