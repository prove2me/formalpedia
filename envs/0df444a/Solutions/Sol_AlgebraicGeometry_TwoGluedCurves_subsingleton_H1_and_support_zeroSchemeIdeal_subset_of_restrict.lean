-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c090e4af-000c-517c-ad04-0d111bcd90ea

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unique_section_of_pullbackSection_closedCover
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv
import Theorems.Thm_AlgebraicGeometry_exists_rationalPoint_enumeration_of_natCard_pullback_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve TensorProduct"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback IsClosedImmersion.of_comp Scheme.Hom GeometricallyIntegral Scheme.Modules.Hom.comp_app Scheme.Modules.Hom IsFinite Spec Scheme Scheme.Modules.Hom.id_app Scheme.Hom.comp_base Scheme.IdealSheafData.comap_id IsClosedImmersion IsReduced Scheme.Hom.comp_app Scheme.Modules.pullbackId Scheme.Modules Scheme.Hom.appLE geometrically Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection OModulePresheaf TwoGluedCurves.eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible OModulePresheaf.cechFinite_ofModules_of_locallyTrivial OModulePresheaf.cechFinite_toOrderedAffineCover_iff Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 Scheme.Modules.exists_unique_section_of_pullbackSection_closedCover Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top exists_rationalPoint_enumeration_of_natCard_pullback_eq Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.Modules.IsInvertible.exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero TwoGluedCurves.exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced"
namespace TwoGluedCurves
p2m_export "AlgebraicGeometry.TwoGluedCurves" "eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced"
namespace K1Crit
p2m_open "AlgebraicGeometry.TwoGluedCurves AlgebraicGeometry"

p2m_open "TopologicalSpace Opposite AlgebraicGeometry.Scheme.Modules"

section Dict

variable {X Y : Scheme.{u}}

lemma map_app {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    N.presheaf.map i.op (φ.app U s) = φ.app V (M.presheaf.map i.op s) := by
  have h := (φ.mapPresheaf).naturality i.op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, U) → Γ(N, V))) h) s).symm

lemma map_homOfLE_rfl {M : X.Modules} {U : X.Opens} (h : U ≤ U) (s : Γ(M, U)) :
    M.presheaf.map (homOfLE h).op s = s := by
  have : homOfLE h = 𝟙 U := Subsingleton.elim _ _
  rw [this, op_id, M.presheaf.map_id]
  rfl

lemma map_toUnitSection_one {U V : X.Opens} (i : V ⟶ U) :
    (𝟙_ X.Modules).presheaf.map i.op (toUnitSection U (1 : Γ(X, U))) = toUnitSection V 1 := by
  apply ofUnitSection_injective
  rw [ofUnitSection_map, ofUnitSection_toUnitSection, ofUnitSection_toUnitSection, map_one]

lemma iso_inv_hom_app_apply {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (x : Γ(N, U)) :
    e.hom.app U (e.inv.app U x) = x := by
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]
  rfl

lemma iso_hom_inv_app_apply {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (x : Γ(M, U)) :
    e.inv.app U (e.hom.app U x) = x := by
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

def gsec {M : X.Modules} (σ : 𝟙_ X.Modules ⟶ M) : Γ(M, ⊤) := σ.app ⊤ (toUnitSection ⊤ 1)

lemma gsec_def {M : X.Modules} (σ : 𝟙_ X.Modules ⟶ M) : gsec σ = σ.app ⊤ (toUnitSection ⊤ 1) := rfl

lemma app_toUnitSection_one {M : X.Modules} (σ : 𝟙_ X.Modules ⟶ M) (U : X.Opens) :
    σ.app U (toUnitSection U 1) = M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (gsec σ) := by
  rw [gsec_def, map_app, map_toUnitSection_one]

lemma hom_ext_of_gsec_eq {M : X.Modules} {σ σ' : 𝟙_ X.Modules ⟶ M} (h : gsec σ = gsec σ') : σ = σ' := by
  apply (SheafOfModules.unitHomEquiv M).injective
  apply PresheafOfModules.sections_ext
  intro U
  change σ.app U.unop (toUnitSection U.unop 1) = σ'.app U.unop (toUnitSection U.unop 1)
  rw [app_toUnitSection_one, app_toUnitSection_one, h]

def sectionsOfGsec {M : X.Modules} (s : Γ(M, ⊤)) : (show SheafOfModules X.ringCatSheaf from M).sections :=
  PresheafOfModules.sectionsMk (M := M.val) (fun U => (M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op s :))
    (by
      intro U V f
      change M.presheaf.map f (M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op s) =
        M.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op s
      rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
      rfl)

def homOfGsec {M : X.Modules} (s : Γ(M, ⊤)) : 𝟙_ X.Modules ⟶ M :=
  (SheafOfModules.unitHomEquiv M).symm (sectionsOfGsec s)

lemma gsec_homOfGsec {M : X.Modules} (s : Γ(M, ⊤)) : gsec (homOfGsec s) = s := by
  have h := congrArg (fun t => PresheafOfModules.sections.eval t (op ⊤))
    ((SheafOfModules.unitHomEquiv M).apply_symm_apply (sectionsOfGsec s))
  change gsec (homOfGsec s) = M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op s at h
  rw [h, map_homOfLE_rfl]

lemma app_pullbackSection_toUnitSection_one (φ : X ⟶ Y) {L : Y.Modules} (σ : 𝟙_ Y.Modules ⟶ L)
    (U : Y.Opens) :
    (pullbackSection φ σ).app (φ ⁻¹ᵁ U) (toUnitSection (φ ⁻¹ᵁ U) 1) =
      pullbackLocalSection φ (σ.app U (toUnitSection U 1)) := by
  rw [pullbackSection_def]
  change ((Scheme.Modules.pullback φ).map σ).app (φ ⁻¹ᵁ U)
      ((pullbackUnitIso φ).inv.app (φ ⁻¹ᵁ U) (toUnitSection (φ ⁻¹ᵁ U) 1)) = _
  have h1 : toUnitSection (φ ⁻¹ᵁ U) (1 : Γ(X, φ ⁻¹ᵁ U)) = toUnitSection (φ ⁻¹ᵁ U) (φ.app U 1) := by
    rw [map_one]
  rw [h1, ← pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection φ U 1, iso_hom_inv_app_apply]
  exact (pullbackLocalSection_app φ σ (toUnitSection U 1)).symm

lemma gsec_pullbackSection (φ : X ⟶ Y) {L : Y.Modules} (σ : 𝟙_ Y.Modules ⟶ L) :
    gsec (pullbackSection φ σ) = pullbackLocalSection φ (gsec σ) :=
  app_pullbackSection_toUnitSection_one φ σ ⊤

lemma pullbackComp_hom_app_app_pullbackLocalSection {Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (s : Γ(M, U)) :
    ((pullbackComp g f).hom.app M).app (g ⁻¹ᵁ (f ⁻¹ᵁ U))
        (pullbackLocalSection g (pullbackLocalSection f s)) =
      pullbackLocalSection (g ≫ f) s := by
  have h := congrArg (fun k => (ConcreteCategory.hom k) s) (unit_app_comp_pullbackComp_inv g f M U)
  simp only [CategoryTheory.comp_apply] at h
  change ((pullbackComp g f).inv.app M).app _ (pullbackLocalSection (g ≫ f) s) =
    pullbackLocalSection g (pullbackLocalSection f s) at h
  rw [← h]
  exact iso_inv_hom_app_apply ((pullbackComp g f).app M) _ _

end Dict

theorem finite_H0_H1 {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover) :
    Module.Finite k (𝒱.sectionsOf x M).H0 ∧ Module.Finite k (𝒱.sectionsOf x M).H1 := by
  have h := AlgebraicGeometry.OModulePresheaf.cechFinite_ofModules_of_locallyTrivial x M
    hM.exists_trivialization 𝒱.toOrderedAffineCover
  rw [AlgebraicGeometry.OModulePresheaf.cechFinite_toOrderedAffineCover_iff] at h
  exact h

theorem hom_eq_zero_of_finrank_H0_eq_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover)
    (h0 : Module.finrank k (𝒱.sectionsOf x M).H0 = 0) (σ : 𝟙_ X.Modules ⟶ M) : σ = 0 := by
  haveI := (finite_H0_H1 x M hM 𝒱).1
  haveI : Subsingleton (𝒱.sectionsOf x M).H0 := Module.finrank_zero_iff.mp h0
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
  obtain ⟨e, -⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 x M
  haveI : Subsingleton Γ(M, ⊤) := e.toEquiv.subsingleton
  exact hom_ext_of_gsec_eq (Subsingleton.elim _ _)

lemma pullbackSection_zero {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    Scheme.Modules.pullbackSection f (0 : 𝟙_ Y.Modules ⟶ M) = 0 := by
  apply hom_ext_of_gsec_eq
  rw [gsec_pullbackSection]
  have hz : gsec (0 : 𝟙_ Y.Modules ⟶ M) = 0 := rfl
  have hz' : gsec (0 : 𝟙_ X.Modules ⟶ (Scheme.Modules.pullback f).obj M) = 0 := rfl
  rw [hz, hz']
  exact pullbackLocalSection_zero _

lemma pullbackSection_comp_eq_zero {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) {L : X.Modules}
    (σ : 𝟙_ X.Modules ⟶ L) (h : Scheme.Modules.pullbackSection (g ≫ f) σ = 0) :
    Scheme.Modules.pullbackSection g (Scheme.Modules.pullbackSection f σ) = 0 := by
  apply hom_ext_of_gsec_eq
  rw [gsec_pullbackSection, gsec_pullbackSection]
  have hinj : Function.Injective (((pullbackComp g f).hom.app L).app (g ⁻¹ᵁ (f ⁻¹ᵁ ⊤))) :=
    (ConcreteCategory.bijective_of_isIso _).1
  apply hinj
  have e := pullbackComp_hom_app_app_pullbackLocalSection g f L ⊤ (gsec σ)
  rw [← gsec_pullbackSection (g ≫ f) σ, h] at e
  have hz : gsec (0 : 𝟙_ Z.Modules ⟶
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj L)) = 0 := rfl
  have hz' : gsec (0 : 𝟙_ Z.Modules ⟶ (Scheme.Modules.pullback (g ≫ f)).obj L) = 0 := rfl
  rw [hz]
  rw [hz'] at e
  exact e.trans (map_zero _).symm

theorem pullbackSection_fst_pullbackSection_eq_zero {X Z₁ Z₂ : Scheme.{u}} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    (L : X.Modules) (σ : 𝟙_ X.Modules ⟶ L) (h₂ : Scheme.Modules.pullbackSection i₂ σ = 0) :
    Scheme.Modules.pullbackSection (pullback.fst i₁ i₂) (Scheme.Modules.pullbackSection i₁ σ) = 0 := by
  apply hom_ext_of_gsec_eq
  rw [gsec_pullbackSection, gsec_pullbackSection]
  have hz : gsec (0 : 𝟙_ (pullback i₁ i₂).Modules ⟶
      (Scheme.Modules.pullback (pullback.fst i₁ i₂)).obj ((Scheme.Modules.pullback i₁).obj L)) = 0 := rfl
  rw [hz]
  have key : pullbackLocalSection (pullback.fst i₁ i₂ ≫ i₁) (gsec σ) = 0 := by
    have hgen : ∀ (f g : pullback i₁ i₂ ⟶ X), f = g → pullbackLocalSection g (gsec σ) = 0 →
        pullbackLocalSection f (gsec σ) = 0 := by
      rintro f g rfl h; exact h
    refine hgen _ _ pullback.condition ?_
    have e := pullbackComp_hom_app_app_pullbackLocalSection (pullback.snd i₁ i₂) i₂ L ⊤ (gsec σ)
    have h : pullbackLocalSection i₂ (gsec σ) =
        (0 : Γ((Scheme.Modules.pullback i₂).obj L, i₂ ⁻¹ᵁ ⊤)) := by
      rw [← gsec_pullbackSection, h₂]; rfl
    rw [h, pullbackLocalSection_zero] at e
    exact e.symm.trans (map_zero _)
  have hinj : Function.Injective
      (((pullbackComp (pullback.fst i₁ i₂) i₁).hom.app L).app ((pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ ⊤))) :=
    (ConcreteCategory.bijective_of_isIso _).1
  apply hinj
  have e := pullbackComp_hom_app_app_pullbackLocalSection (pullback.fst i₁ i₂) i₁ L ⊤ (gsec σ)
  exact (e.trans key).trans (map_zero _).symm

theorem eq_zero_of_pullbackSection_eq_zero_of_closedCover {X Z₁ Z₂ : Scheme.{u}}
    (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsReduced X]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (σ : 𝟙_ X.Modules ⟶ L)
    (h₁ : Scheme.Modules.pullbackSection i₁ σ = 0) (h₂ : Scheme.Modules.pullbackSection i₂ σ = 0) : σ = 0 := by
  obtain ⟨τ, -, -, huniq⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_unique_section_of_pullbackSection_closedCover i₁ i₂ hcover L hL 0 0
      (by simp only [pullbackSection_zero, zero_comp])
  exact (huniq σ h₁ h₂).trans
    (huniq 0 (pullbackSection_zero _ _) (pullbackSection_zero _ _)).symm

theorem exists_linearMap_pullbackLocalSection
    {R : Type u} [CommRing R] {X Y : Scheme.{u}} (x : X ⟶ Spec (.of R)) (y : Y ⟶ Spec (.of R))
    (i : Y ⟶ X) (hi : i ≫ x = y) (M : X.Modules) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom y ((Scheme.Modules.pullback i).obj M) ⊤
    ∃ ρ : Γ(M, ⊤) →ₗ[R] Γ((Scheme.Modules.pullback i).obj M, ⊤),
      ∀ s : Γ(M, ⊤), ρ s = pullbackLocalSection i s := by
  subst hi
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (i ≫ x) ((Scheme.Modules.pullback i).obj M) ⊤
  have keyh : x.appLE ⊤ ⊤ le_top ≫ i.app ⊤ = (i ≫ x).appLE ⊤ ⊤ le_top := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Category.assoc]
    erw [i.naturality]
    rfl
  have key : ∀ a : Γ(Spec (.of R), ⊤), i.app ⊤ (x.appLE ⊤ ⊤ le_top a) = (i ≫ x).appLE ⊤ ⊤ le_top a := by
    intro a
    rw [← keyh]
    rfl
  refine ⟨{ toFun := fun s => pullbackLocalSection i s
            map_add' := fun s s' => pullbackLocalSection_add i s s'
            map_smul' := fun r s => ?_ }, fun s => rfl⟩
  change pullbackLocalSection i (((Scheme.TwoAffineOpenCover.algebraOfHom x ⊤).algebraMap r) • s) =
    (show Γ(Y, i ⁻¹ᵁ ⊤) from ((Scheme.TwoAffineOpenCover.algebraOfHom (i ≫ x) ⊤).algebraMap r)) •
      pullbackLocalSection i s
  rw [pullbackLocalSection_smul, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,
    Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, key]

theorem eq_zero_of_pullbackSection_snd_eq_zero
    {k : Type u} [Field k] {X C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) [IsProper c₁]
    (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsReduced X]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hI : (pullback.fst i₁ i₂).ker.IsInvertible) (𝒱₁ : C₁.TwoAffineOpenCover)
    (h10 : Module.finrank k (𝒱₁.sectionsOf c₁
      ((Scheme.Modules.pullback i₁).obj M ⊗ ((pullback.fst i₁ i₂).ker).module)).H0 = 0)
    (σ : 𝟙_ X.Modules ⟶ M) (h₂ : Scheme.Modules.pullbackSection i₂ σ = 0) : σ = 0 := by
  have hfst := pullbackSection_fst_pullbackSection_eq_zero i₁ i₂ M σ h₂
  obtain ⟨s', hs'⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero (pullback.fst i₁ i₂) (hM.pullback i₁) _ hfst
  have hinv : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback i₁).obj M ⊗ ((pullback.fst i₁ i₂).ker).module) :=
    (hM.pullback i₁).tensor hI.isInvertible_module
  have hs'0 : s' = 0 := hom_eq_zero_of_finrank_H0_eq_zero c₁ _ hinv 𝒱₁ h10 s'
  have h₁ : Scheme.Modules.pullbackSection i₁ σ = 0 := by rw [← hs', hs'0, zero_comp]
  exact eq_zero_of_pullbackSection_eq_zero_of_closedCover i₁ i₂ hcover M hM σ h₁ h₂

theorem finrank_H0_le_one
    {k : Type u} [Field k] {X C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (c₂ : C₂ ⟶ Spec (CommRingCat.of k)) (i₂ : C₂ ⟶ X) (hi₂ : i₂ ≫ x = c₂) (M : X.Modules)
    (hvan : ∀ σ : 𝟙_ X.Modules ⟶ M, Scheme.Modules.pullbackSection i₂ σ = 0 → σ = 0)
    (𝒱 : X.TwoAffineOpenCover) (𝒱₂ : C₂.TwoAffineOpenCover)
    (h20 : Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂).obj M)).H0 = 1) :
    Module.finrank k (𝒱.sectionsOf x M).H0 ≤ 1 := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c₂ ((Scheme.Modules.pullback i₂).obj M) ⊤
  obtain ⟨e, -⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 x M
  obtain ⟨e₂, -⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱₂ c₂
    ((Scheme.Modules.pullback i₂).obj M)
  obtain ⟨ρ, hρ⟩ := exists_linearMap_pullbackLocalSection x c₂ i₂ hi₂ M
  have hinj : Function.Injective ρ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    have hσ : Scheme.Modules.pullbackSection i₂ (homOfGsec s) = 0 := by
      apply hom_ext_of_gsec_eq
      rw [gsec_pullbackSection, gsec_homOfGsec]
      exact (hρ s).symm.trans hs
    have h0 := hvan _ hσ
    rw [← gsec_homOfGsec s, h0]
    rfl
  haveI : Module.Finite k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂).obj M)).H0 :=
    Module.finite_of_finrank_eq_succ h20
  haveI : Module.Finite k Γ((Scheme.Modules.pullback i₂).obj M, ⊤) := Module.Finite.equiv e₂.symm
  calc Module.finrank k (𝒱.sectionsOf x M).H0 = Module.finrank k Γ(M, ⊤) := e.finrank_eq.symm
    _ ≤ Module.finrank k Γ((Scheme.Modules.pullback i₂).obj M, ⊤) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂).obj M)).H0 := e₂.finrank_eq
    _ = 1 := h20

theorem subsingleton_H1_of_eulerChar
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover)
    (hχ : (Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1 = 1)
    (h0 : Module.finrank k (𝒱.sectionsOf x M).H0 ≤ 1) :
    Subsingleton (𝒱.sectionsOf x M).H1 := by
  haveI := (finite_H0_H1 x M hM 𝒱).2
  have h1 : Module.finrank k (𝒱.sectionsOf x M).H1 = 0 := by omega
  exact Module.finrank_zero_iff.mp h1

def χ {k : Type u} [Field k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (x : X ⟶ Spec (CommRingCat.of k))
    (M : X.Modules) : ℤ :=
  (Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1

theorem χ_def {k : Type u} [Field k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (x : X ⟶ Spec (CommRingCat.of k))
    (M : X.Modules) :
    χ 𝒱 x M = (Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1 := rfl

theorem χ_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') : χ 𝒱 x M = χ 𝒱 x M' := by
  obtain ⟨𝒲, hU0, hU1, ⟨f0⟩, ⟨f1⟩⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X)
      (Category.id_comp x) 𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒲 = 𝒱 := by
    cases 𝒲; cases 𝒱
    simp only at hU0 hU1
    subst hU0; subst hU1
    rfl
  rw [χ_def, χ_def, f0.finrank_eq, f1.finrank_eq]

theorem χ_pullbackId {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) :
    χ 𝒱 x ((Scheme.Modules.pullback (𝟙 X)).obj M) = χ 𝒱 x M :=
  χ_congr x 𝒱 ((Scheme.Modules.pullbackId X).app M)

theorem isInvertible_ker_fst_and_eulerChar_eq
    (k : Type u) [Field k] [IsAlgClosed k] {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [IsProper c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱₁ : C₁.TwoAffineOpenCover) :
    (pullback.fst i₁.1 i₂.1).ker.IsInvertible ∧
    ((Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj M)).H0 : ℤ) -
        Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj M)).H1 =
      (Module.finrank k (𝒱₁.sectionsOf c₁
          ((Scheme.Modules.pullback i₁.1).obj M ⊗ ((pullback.fst i₁.1 i₂.1).ker).module)).H0 : ℤ) -
        Module.finrank k (𝒱₁.sectionsOf c₁
          ((Scheme.Modules.pullback i₁.1).obj M ⊗ ((pullback.fst i₁.1 i₂.1).ker).module)).H1 + n) := by
  classical
  obtain ⟨S, hS, hprod, -, -⟩ := AlgebraicGeometry.TwoGluedCurves.exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced k x c₁ c₂ i₁ i₂ hred n hn hn0
  have hinvS : ∀ p ∈ S, p.1.ker.IsInvertible := fun p _ =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := c₁) p.1 p.2
  have hI : (pullback.fst i₁.1 i₂.1).ker.IsInvertible := by
    rw [← hprod]
    exact Finset.prod_induction _ (fun I : C₁.IdealSheafData => I.IsInvertible)
      (fun _ _ h h' => h.mul h') Scheme.IdealSheafData.isInvertible_top hinvS
  refine ⟨hI, ?_⟩

  set L := (Scheme.Modules.pullback i₁.1).obj M with hL
  have hLinv : Scheme.Modules.IsInvertible L := hM.pullback i₁.1
  have hpt : ∀ p ∈ S, IsFinite ((p.1.ker.comap (𝟙 C₁)).subschemeι ≫ c₁) ∧
      ∀ t : Spec (CommRingCat.of k), ((p.1.ker.comap (𝟙 C₁)).subschemeι ≫ c₁).finrank t = 1 := by
    intro p _
    obtain ⟨hf, hd, -, -⟩ := Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (p := c₁) p.1 p.2 1
    rw [pow_one] at hf hd
    rw [Scheme.IdealSheafData.comap_id]
    exact ⟨hf, hd⟩
  obtain ⟨-, hrow⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor
      (𝟙 C₁) c₁ S (fun p => p.1.ker) (fun _ => 1) (fun _ => 1) hinvS
      (fun p hp => by rw [Scheme.IdealSheafData.comap_id]; exact hinvS p hp)
      (fun p hp => (hpt p hp).1) (fun p hp => (hpt p hp).2) L hLinv 𝒱₁

  have hrow' : χ 𝒱₁ c₁ ((Scheme.Modules.pullback (𝟙 C₁)).obj ((∏ p ∈ S, p.1.ker ^ (1:ℕ)).module ⊗ L)) =
      χ 𝒱₁ c₁ ((Scheme.Modules.pullback (𝟙 C₁)).obj L) - ∑ p ∈ S, ((1:ℕ) : ℤ) * ((1:ℕ) : ℤ) := hrow
  rw [χ_pullbackId, χ_pullbackId] at hrow'
  have hsum : ∑ p ∈ S, ((1:ℕ) : ℤ) * ((1:ℕ) : ℤ) = n := by
    simp [Finset.sum_const, hS]
  have hpow : (∏ p ∈ S, p.1.ker ^ (1:ℕ)) = (pullback.fst i₁.1 i₂.1).ker := by
    rw [← hprod]; exact Finset.prod_congr rfl fun _ _ => pow_one _

  have e : L ⊗ ((pullback.fst i₁.1 i₂.1).ker).module ≅ (∏ p ∈ S, p.1.ker ^ (1:ℕ)).module ⊗ L :=
    (β_ _ _) ≪≫ eqToIso (by rw [hpow])
  have hχe := χ_congr c₁ 𝒱₁ e
  show χ 𝒱₁ c₁ L = χ 𝒱₁ c₁ (L ⊗ ((pullback.fst i₁.1 i₂.1).ker).module) + n
  rw [hχe, hrow', hsum]
  ring

theorem support_zeroSchemeIdeal_subset_compl_range
    (k : Type u) [Field k] [IsAlgClosed k] {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [IsProper c₂] [SmoothOfRelativeDimension 1 c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hvan : ∀ σ : 𝟙_ X.Modules ⟶ M, Scheme.Modules.pullbackSection i₂.1 σ = 0 → σ = 0)
    (𝒱₂ : C₂.TwoAffineOpenCover)
    (h3 : ∀ p : Spec (CommRingCat.of k) ⟶ C₂, p ≫ c₂ = 𝟙 _ →
      Set.range (p ≫ i₂.1).base ⊆ Set.range i₁.1.base →
      Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj M ⊗ (p.ker).module)).H0 = 0)
    (σ : 𝟙_ X.Modules ⟶ M) (hσ : σ ≠ 0) :
    ((Scheme.Modules.zeroSchemeIdeal σ).support : Set X) ⊆ (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ := by
  intro z hz hzr
  obtain ⟨q, rfl⟩ := hzr
  obtain ⟨p₁, p₂, -, hnode, hinter⟩ :=
    AlgebraicGeometry.exists_rationalPoint_enumeration_of_natCard_pullback_eq k x i₁ i₂ n hn hn0
  have hcond : i₁.1.base ((pullback.fst i₁.1 i₂.1).base q) = i₂.1.base ((pullback.snd i₁.1 i₂.1).base q) := by
    have := congrArg (fun f : pullback i₁.1 i₂.1 ⟶ X => f.base q) (pullback.condition (f := i₁.1) (g := i₂.1))
    simpa using this
  obtain ⟨j, hj₁, hj₂⟩ := hinter _ _ hcond
  set p := (p₂ j).1 with hpdef
  have hp : p ≫ c₂ = 𝟙 _ := (p₂ j).2
  have hzpt : (p ≫ i₂.1).base (IsLocalRing.closedPoint k) = (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base q := by
    rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.comp_app, TopCat.comp_app, ← hj₂, hcond]

  have h0 : Scheme.Modules.pullbackSection (p ≫ i₂.1) σ = 0 :=
    (hM.pullbackSection_eq_zero_iff_mem_support σ (p ≫ i₂.1)).mpr (hzpt ▸ hz)
  have h0' : Scheme.Modules.pullbackSection p (Scheme.Modules.pullbackSection i₂.1 σ) = 0 :=
    pullbackSection_comp_eq_zero p i₂.1 σ h0
  haveI : IsClosedImmersion (p ≫ c₂) := by rw [hp]; infer_instance
  haveI : IsClosedImmersion p := IsClosedImmersion.of_comp p c₂
  obtain ⟨s', hs'⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero p (hM.pullback i₂.1) _ h0'
  have hinv : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback i₂.1).obj M ⊗ (p.ker).module) :=
    (hM.pullback i₂.1).tensor (Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := c₂) p hp).isInvertible_module
  have hrange : Set.range (p ≫ i₂.1).base ⊆ Set.range i₁.1.base := by
    rintro _ ⟨t, rfl⟩
    obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    exact ⟨(pullback.fst i₁.1 i₂.1).base q, by rw [hzpt]; rfl⟩
  have hs'0 : s' = 0 := hom_eq_zero_of_finrank_H0_eq_zero c₂ _ hinv 𝒱₂ (h3 p hp hrange) s'
  have h2 : Scheme.Modules.pullbackSection i₂.1 σ = 0 := by rw [← hs', hs'0, zero_comp]
  exact hσ (hvan σ h2)

end AlgebraicGeometry.TwoGluedCurves.K1Crit

open AlgebraicGeometry.TwoGluedCurves.K1Crit in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [IsReduced X]
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (𝒱₁ : C₁.TwoAffineOpenCover) (𝒱₂ : C₂.TwoAffineOpenCover)

    (h1 : Module.finrank k (𝒱₁.sectionsOf c₁
        ((Scheme.Modules.pullback i₁.1).obj M ⊗ ((pullback.fst i₁.1 i₂.1).ker).module)).H0 = 0 ∧
      Subsingleton (𝒱₁.sectionsOf c₁
        ((Scheme.Modules.pullback i₁.1).obj M ⊗ ((pullback.fst i₁.1 i₂.1).ker).module)).H1)

    (h2 : Subsingleton (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj M)).H1 ∧
      Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj M)).H0 = 1)

    (h3 : ∀ p : Spec (CommRingCat.of k) ⟶ C₂, p ≫ c₂ = 𝟙 _ →
      Set.range (p ≫ i₂.1).base ⊆ Set.range i₁.1.base →
      Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj M ⊗ (p.ker).module)).H0 = 0) :
    (∀ 𝒱 : X.TwoAffineOpenCover, Subsingleton (𝒱.sectionsOf x M).H1) ∧
    ∀ σ : 𝟙_ X.Modules ⟶ M, σ ≠ 0 →
      ((Scheme.Modules.zeroSchemeIdeal σ).support : Set X) ⊆ (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ := by
  have hcov : Set.range i₁.1.base ∪ Set.range i₂.1.base = Set.univ :=
    Set.eq_univ_of_forall fun z => (hcover z).elim (fun h => Or.inl h) (fun h => Or.inr h)
  have hfin : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨hI, htwist⟩ := isInvertible_ker_fst_and_eulerChar_eq k x c₁ c₂ i₁ i₂ hred n hn hn0 M hM 𝒱₁
  have hvan : ∀ σ : 𝟙_ X.Modules ⟶ M, Scheme.Modules.pullbackSection i₂.1 σ = 0 → σ = 0 := fun σ h =>
    eq_zero_of_pullbackSection_snd_eq_zero c₁ i₁.1 i₂.1 hcov M hM hI 𝒱₁ h1.1 σ h
  refine ⟨fun 𝒱 => ?_, fun σ hσ =>
    support_zeroSchemeIdeal_subset_compl_range k x c₁ c₂ i₁ i₂ n hn hn0 M hM hvan 𝒱₂ h3 σ hσ⟩
  have hχ := AlgebraicGeometry.TwoGluedCurves.eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible k x c₁ c₂
    i₁ i₂ hcover hred hfin n hn M hM 𝒱 𝒱₁ 𝒱₂
  have h21 : Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj M)).H1 = 0 := by
    haveI := h2.1; exact Module.finrank_zero_of_subsingleton
  have h11 : Module.finrank k (𝒱₁.sectionsOf c₁
      ((Scheme.Modules.pullback i₁.1).obj M ⊗ ((pullback.fst i₁.1 i₂.1).ker).module)).H1 = 0 := by
    haveI := h1.2; exact Module.finrank_zero_of_subsingleton
  have hle := finrank_H0_le_one x c₂ i₂.1 i₂.2 M hvan 𝒱 𝒱₂ h2.2
  refine subsingleton_H1_of_eulerChar x M hM 𝒱 ?_ hle
  rw [hχ, htwist, h1.1, h11, h2.2, h21]
  push_cast
  ring

end
end S_AlgebraicGeometry_TwoGluedCurves_subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_subsingleton_H1_and_support_zeroSchemeIdeal_subset_of_restrict (solution)
