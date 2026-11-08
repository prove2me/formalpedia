-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeH0
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNativeH0
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T12:19:21.764687+00:00
-- url     : https://prove2.me/theorems/1272edfb-a11f-4ad4-a832-a8f00848795d
-- title:
--   LPSOriginal Native H0
-- statement:
--   Definitions and structural lemmas for LPSOriginal Native H0, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeH0.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeGlobalRegularity
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialChartImageKaehlerIso_inv_global
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialGlobalRestrictionToKaehler_smul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGlobalConstantMap_zero_affine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeGlobalGenericDifferential_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeGlobalGenericDifferential_noPole
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeNoPole_existsUnique_globalDifferentialSection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTwoAffineKaehlerRanges_iff_allNativeNoPole

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped _root_.AlgebraicGeometry MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "c" => lpsOriginalComplexNormalGlobalConstantMap N hpos
local notation "Omega" => lpsOriginalComplexNormalDifferentialSheaf N hpos
local notation "f0" => lpsOriginalComplexNormalGluedChartMap N hpos false
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
attribute [local instance]
  LPSOriginalAffineKaehlerCompatibilityDictionary001
  LPSOriginalAffineKaehlerCompatibilityDictionary002
  LPSOriginalAffineKaehlerCompatibilityDictionary003
  LPSOriginalAffineKaehlerCompatibilityDictionary004
  LPSOriginalAffineKaehlerCompatibilityDictionary011
  LPSOriginalAffineKaehlerCompatibilityDictionary012
  LPSOriginalAffineKaehlerCompatibilityDictionary013
  LPSOriginalAffineKaehlerCompatibilityDictionary014
  LPSOriginalAffineKaehlerCompatibilityDictionary023
  LPSOriginalAffineKaehlerCompatibilityDictionary024
  LPSOriginalAffineKaehlerCompatibilityDictionary025
  LPSOriginalAffineKaehlerCompatibilityDictionary026
attribute [local instance] LPSOriginalAffineKaehlerCompatibilityDictionary027
  LPSOriginalAffineKaehlerCompatibilityDictionary034
  LPSOriginalAffineKaehlerCompatibilityDictionary035
  LPSOriginalAffineKaehlerCompatibilityDictionary036
  LPSOriginalAffineKaehlerCompatibilityDictionary037
  LPSOriginalAffineKaehlerCompatibilityDictionary041
  LPSOriginalAffineKaehlerCompatibilityDictionary050
local instance originalNativeGlobalComplexModule : Module ℂ Γ(Omega, ⊤) :=
  schemeDifferentialGlobalConstantModule ℂ X c
local notation "U" => Functor.obj (Scheme.Hom.opensFunctor (f0)) ⊤
def lpsOriginalNativeGlobalGenericDifferentialAddHom : Γ(Omega, ⊤) →+ KaehlerDifferential ℂ K :=
  (KaehlerDifferential.map ℂ ℂ R K).toAddMonoidHom.comp
    ((lpsOriginalZeroImageFromKaehler N hpos).inv.hom.comp
      ((Omega).presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom)
lemma lpsOriginalNativeGlobalZeroProjection_eq_restriction (z : Γ(Omega, ⊤)) :
    (lpsOriginalNativeGlobalAffinePair N hpos z).1 =
      @affineDifferentialGlobalRestrictionToKaehler ℂ inferInstance X c
        (CommRingCat.of R) inferInstance (f0) (originalNativeGlobalZeroOpen N hpos)
        (lpsOriginalComplexNormalGlobalConstantMap_zero_affine N hpos) z :=
  @affineDifferentialChartImageKaehlerIso_inv_global ℂ inferInstance X c
    (CommRingCat.of R) inferInstance (f0) (originalNativeGlobalZeroOpen N hpos)
    (lpsOriginalComplexNormalGlobalConstantMap_zero_affine N hpos) z
lemma lpsOriginalNativeGlobalZeroProjection_smul (r : ℂ) (z : Γ(Omega, ⊤)) :
    (lpsOriginalNativeGlobalAffinePair N hpos (r • z)).1 =
      r • (lpsOriginalNativeGlobalAffinePair N hpos z).1 := by
  have h0 := lpsOriginalNativeGlobalZeroProjection_eq_restriction N hpos (r • z)
  have h1 := @affineDifferentialGlobalRestrictionToKaehler_smul ℂ inferInstance X c
    (CommRingCat.of R) inferInstance (f0) (originalNativeGlobalZeroOpen N hpos)
    (lpsOriginalComplexNormalGlobalConstantMap_zero_affine N hpos) r z
  have h2 := congrArg (fun t : KaehlerDifferential ℂ R => r • t)
    (lpsOriginalNativeGlobalZeroProjection_eq_restriction N hpos z).symm
  exact h0.trans (h1.trans h2)
lemma lpsOriginalNativeGlobalGenericDifferential_smul (r : ℂ) (z : Γ(Omega, ⊤)) :
    lpsOriginalNativeGlobalGenericDifferential N hpos (r • z) =
      r • lpsOriginalNativeGlobalGenericDifferential N hpos z :=
  (congrArg (KaehlerDifferential.map ℂ ℂ R K)
    (lpsOriginalNativeGlobalZeroProjection_smul N hpos r z)).trans
      ((KaehlerDifferential.map ℂ ℂ R K).map_smul_of_tower r
        (lpsOriginalNativeGlobalAffinePair N hpos z).1)
def lpsOriginalNativeGlobalGenericDifferentialLinearMap :
    Γ(Omega, ⊤) →ₗ[ℂ] KaehlerDifferential ℂ K where
  __ := lpsOriginalNativeGlobalGenericDifferentialAddHom N hpos
  map_smul' r z := lpsOriginalNativeGlobalGenericDifferential_smul N hpos r z
def lpsOriginalNativeRegularKaehlerSubmodule : Submodule ℂ (KaehlerDifferential ℂ K) :=
  (KaehlerDifferential.map ℂ ℂ R K).range.restrictScalars ℂ ⊓
    (KaehlerDifferential.map ℂ ℂ I K).range.restrictScalars ℂ
lemma lpsOriginalNativeRegularKaehlerSubmodule_mem_iff (omega : KaehlerDifferential ℂ K) :
    omega ∈ lpsOriginalNativeRegularKaehlerSubmodule N hpos ↔
    ∀ x : LPSOriginalFilledCurve N, 0 ≤ meromorphicOrderValuation
      (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega)) :=
  lpsOriginalTwoAffineKaehlerRanges_iff_allNativeNoPole N hpos hN omega
include hN in
lemma lpsOriginalNativeGlobalGenericDifferentialLinearMap_mem
    (z : Γ(Omega, ⊤)) :
    lpsOriginalNativeGlobalGenericDifferentialLinearMap N hpos z ∈
      lpsOriginalNativeRegularKaehlerSubmodule N hpos := by
  apply (lpsOriginalNativeRegularKaehlerSubmodule_mem_iff N hpos hN _).mpr
  exact lpsOriginalNativeGlobalGenericDifferential_noPole N hpos hN z
def lpsOriginalNativeH0ToRegularCovectorLinearMap :
    Γ(Omega, ⊤) →ₗ[ℂ] lpsOriginalNativeRegularKaehlerSubmodule N hpos :=
  (lpsOriginalNativeGlobalGenericDifferentialLinearMap N hpos).codRestrict
    (lpsOriginalNativeRegularKaehlerSubmodule N hpos)
    (lpsOriginalNativeGlobalGenericDifferentialLinearMap_mem N hpos hN)
include hN in
lemma lpsOriginalNativeH0ToRegularCovectorLinearMap_bijective :
    Function.Bijective (lpsOriginalNativeH0ToRegularCovectorLinearMap N hpos hN) := by
  constructor
  · intro z z' h
    exact lpsOriginalNativeGlobalGenericDifferential_injective N hpos hN
      (congrArg Subtype.val h)
  · intro omega
    have h := (lpsOriginalNativeRegularKaehlerSubmodule_mem_iff N hpos hN omega.val).mp omega.property
    obtain ⟨z, hz, _⟩ := lpsOriginalNativeNoPole_existsUnique_globalDifferentialSection
      N hpos hN omega.val h
    exact ⟨z, Subtype.ext hz.1⟩
def lpsOriginalNativeH0RegularCovectorLinearEquiv :
    Γ(Omega, ⊤) ≃ₗ[ℂ] lpsOriginalNativeRegularKaehlerSubmodule N hpos :=
  LinearEquiv.ofBijective (lpsOriginalNativeH0ToRegularCovectorLinearMap N hpos hN)
    (lpsOriginalNativeH0ToRegularCovectorLinearMap_bijective N hpos hN)
end
end QEC.Coding.TannerLiftedProduct


