-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a1885ed6-08a3-52a3-82eb-5b3439496d20

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesRigidify

import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_rigidify_lineBundle_tensor_idealModule_and_nonempty_pullback_iso_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_rigidify_iso_of_subsingleton_H1_of_support_subset
import Theorems.Thm_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_opens_range_subset_iff_forall_support_zeroSchemeIdeal_subset_of_forall_fibre
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U1"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.ofPreimage_hom AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.injEq AlgebraicGeometry.RelPicard.LFP.stageHom_val TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P"

set_option autoImplicit false
set_option maxHeartbeats 3200000

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Scheme.Opens.ι_image_le IsOpenImmersion.lift Scheme.IdealSheafData.support_comap SmoothOfRelativeDimension IsProper Scheme.Modules.pullback LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom LocallyOfFiniteType Spec Spec.map Scheme Scheme.Hom.apply_mem_image_iff IsOpenImmersion Flat IsSeparated Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Opens.ι_apply Scheme.Modules IsNoetherian Scheme.Opens IsOpenImmersion.lift_fac Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.rigSection Scheme.IdealSheafData.module RelEffCartierDiv RelEffCartierDiv.ext mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd PullsBackOver pullsBackOver_pullbackAlong PullsBackOver.eq_pullbackAlong RelEffCartierDiv.pullbackAlong_comp mapOnProdOver_snd_assoc Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.Modules.rigidify Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.pullbackSection_def RelEffCartierDiv.isInvertible_I_of_supportedIn Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn RelEffCartierDiv.isInvertible_rigidify_lineBundle_tensor_idealModule_and_nonempty_pullback_iso_of_supportedIn RelEffCartierDiv.nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn Scheme.Modules.pullbackTensorObjIso RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.IdealSheafData.comap_mul Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso algEquivZeroCut RigidifiedLineBundle.pullbackAlongPullbackAlongIso relSubPicPresheaf fibreModule exists_relEffCartierDiv_supportedIn_rigidify_iso_of_subsingleton_H1_of_support_subset relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover exists_opens_range_subset_iff_forall_support_zeroSchemeIdeal_subset_of_forall_fibre"
namespace FinTransport
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard NeronModelInfra"

theorem coe_support_zeroSchemeIdeal_pullbackSection {X X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) :
    ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection F s)).support : Set X') =
      F.base ⁻¹' ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) := by
  rw [← hM.comap_zeroSchemeIdeal F, Scheme.IdealSheafData.support_comap]
  rfl

noncomputable def pullbackEquivOfIso {X X' : Scheme.{u}} (e : X' ≅ X) : X.Modules ≌ X'.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackComp e.inv e.hom ≪≫ Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫
      Scheme.Modules.pullbackId X).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫ Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫
      Scheme.Modules.pullbackId X')

scoped instance full_pullback_of_isIso {X X' : Scheme.{u}} (F : X' ⟶ X) [IsIso F] :
    (Scheme.Modules.pullback F).Full :=
  (pullbackEquivOfIso (asIso F)).full_functor

scoped instance faithful_pullback_of_isIso {X X' : Scheme.{u}} (F : X' ⟶ X) [IsIso F] :
    (Scheme.Modules.pullback F).Faithful :=
  (pullbackEquivOfIso (asIso F)).faithful_functor

theorem pullbackSection_ne_zero_of_isIso {X X' : Scheme.{u}} (F : X' ⟶ X) [IsIso F] {M : X.Modules}
    {s : 𝟙_ X.Modules ⟶ M} (hs : s ≠ 0) : Scheme.Modules.pullbackSection F s ≠ 0 := by
  intro h
  rw [Scheme.Modules.pullbackSection_def] at h
  have h1 : (Scheme.Modules.pullback F).map s = 0 := (Preadditive.IsIso.comp_left_eq_zero _ _).mp h
  exact hs ((Scheme.Modules.pullback F).map_injective
    (h1.trans ((Scheme.Modules.pullback F).map_zero _ _).symm))

theorem exists_pullbackSection_eq_of_isIso {X X' : Scheme.{u}} (F : X' ⟶ X) [IsIso F] {M : X.Modules}
    (τ : 𝟙_ X'.Modules ⟶ (Scheme.Modules.pullback F).obj M) :
    ∃ s : 𝟙_ X.Modules ⟶ M, Scheme.Modules.pullbackSection F s = τ := by
  refine ⟨(Scheme.Modules.pullback F).preimage ((Scheme.Modules.pullbackUnitIso F).hom ≫ τ), ?_⟩
  rw [Scheme.Modules.pullbackSection_def]
  erw [Functor.map_preimage]
  exact (Scheme.Modules.pullbackUnitIso F).inv_hom_id_assoc τ

theorem forall_support_subset_iff_of_isIso {Y Y' : Scheme.{u}} (F : Y' ⟶ Y) [IsIso F] {P : Y.Modules}
    (hP : Scheme.Modules.IsInvertible P) {P' : Y'.Modules} (j : P' ≅ (Scheme.Modules.pullback F).obj P)
    (V : Set Y) :
    (∀ σ' : 𝟙_ Y'.Modules ⟶ P', σ' ≠ 0 →
        ((Scheme.Modules.zeroSchemeIdeal σ').support : Set Y') ⊆ F.base ⁻¹' V) ↔
      (∀ σ : 𝟙_ Y.Modules ⟶ P, σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set Y) ⊆ V) := by
  constructor
  · intro h σ hσ
    have hσ' : Scheme.Modules.pullbackSection F σ ≫ j.inv ≠ 0 := fun h0 =>
      pullbackSection_ne_zero_of_isIso F hσ ((Preadditive.IsIso.comp_right_eq_zero _ _).mp h0)
    have := h _ hσ'
    rw [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
      coe_support_zeroSchemeIdeal_pullbackSection F hP] at this
    exact F.homeomorph.surjective.preimage_subset_preimage_iff.mp this
  · intro h σ' hσ'
    obtain ⟨σ, hσ⟩ := exists_pullbackSection_eq_of_isIso F (σ' ≫ j.hom)
    have hσ0 : σ ≠ 0 := by
      intro hz
      apply hσ'
      have h1 : σ' ≫ j.hom = 0 := by
        rw [← hσ, Scheme.Modules.pullbackSection_def, hz]
        exact (congrArg ((Scheme.Modules.pullbackUnitIso F).inv ≫ ·)
          ((Scheme.Modules.pullback F).map_zero _ _)).trans comp_zero
      exact (Preadditive.IsIso.comp_right_eq_zero _ _).mp h1
    have := h σ hσ0
    rw [← Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso σ' j.hom, ← hσ,
      coe_support_zeroSchemeIdeal_pullbackSection F hP]
    exact Set.preimage_mono this

abbrev FinerAt {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) : Prop :=
  ∀ σ : 𝟙_ (pullback c (s ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj M,
    σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (s ≫ t))) ⊆
      ((pullback.fst c (s ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫ t)))

theorem finerAt_transport {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (U : C.Opens) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : SchemeHomOver t' t) (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (M' : (pullback c t').Modules) (i : M' ≅ (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj M)
    {k : Type u} [Field k] (x' : Spec (CommRingCat.of k) ⟶ T') :
    FinerAt c U t' M' x' ↔ FinerAt c U t M (x' ≫ ψ.1) := by
  obtain ⟨ψ1, hψ⟩ := ψ
  subst hψ

  let e : pullback c (x' ≫ ψ1 ≫ t) ≅ pullback c ((x' ≫ ψ1) ≫ t) :=
    pullback.congrHom rfl (Category.assoc _ _ _).symm
  have he_fst : e.hom ≫ pullback.fst c ((x' ≫ ψ1) ≫ t) = pullback.fst c (x' ≫ ψ1 ≫ t) := by
    rw [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  have hE : mapOnProdOver c x' rfl ≫ baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t) =
      e.hom ≫ mapOnProdOver c (x' ≫ ψ1) rfl := by
    apply pullback.hom_ext
    · simp only [e, Category.assoc, mapOnProdOver_fst, pullback.congrHom_hom, baseChangeSnd, pullback.lift_fst,
        Category.comp_id]
    · simp only [e, Category.assoc, mapOnProdOver_snd, pullback.congrHom_hom, baseChangeSnd, pullback.lift_snd,
        Category.comp_id, mapOnProdOver_snd_assoc, pullback.lift_snd_assoc]
  have hP : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (mapOnProdOver c (x' ≫ ψ1) rfl)).obj M) :=
    hM.pullback _
  let j : (Scheme.Modules.pullback (mapOnProdOver c x' rfl)).obj M' ≅
      (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback (mapOnProdOver c (x' ≫ ψ1) rfl)).obj M) :=
    (Scheme.Modules.pullback (mapOnProdOver c x' rfl)).mapIso i ≪≫
      (Scheme.Modules.pullbackComp (mapOnProdOver c x' rfl) (baseChangeSnd c ⟨ψ1, rfl⟩)).app M ≪≫
      (Scheme.Modules.pullbackCongr hE).app M ≪≫
      ((Scheme.Modules.pullbackComp e.hom (mapOnProdOver c (x' ≫ ψ1) rfl)).app M).symm
  have hV : e.hom.base ⁻¹' ((pullback.fst c ((x' ≫ ψ1) ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c ((x' ≫ ψ1) ≫ t))) =
      ((pullback.fst c (x' ≫ ψ1 ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x' ≫ ψ1 ≫ t))) := by
    rw [← he_fst]
    rfl
  have key := forall_support_subset_iff_of_isIso e.hom hP j
    ((pullback.fst c ((x' ≫ ψ1) ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c ((x' ≫ ψ1) ≫ t)))
  rw [hV] at key
  exact key

end AlgebraicGeometry.RelPicard.FinTransport
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard.FinTransport"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Scheme.Opens.ι_image_le IsOpenImmersion.lift Scheme.IdealSheafData.support_comap SmoothOfRelativeDimension IsProper Scheme.Modules.pullback LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom LocallyOfFiniteType Spec Spec.map Scheme Scheme.Hom.apply_mem_image_iff IsOpenImmersion Flat IsSeparated Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Opens.ι_apply Scheme.Modules IsNoetherian Scheme.Opens IsOpenImmersion.lift_fac Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.rigSection Scheme.IdealSheafData.module RelEffCartierDiv RelEffCartierDiv.ext mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd PullsBackOver pullsBackOver_pullbackAlong PullsBackOver.eq_pullbackAlong RelEffCartierDiv.pullbackAlong_comp mapOnProdOver_snd_assoc Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom Scheme.Modules.rigidify Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.pullbackSection_def RelEffCartierDiv.isInvertible_I_of_supportedIn Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn RelEffCartierDiv.isInvertible_rigidify_lineBundle_tensor_idealModule_and_nonempty_pullback_iso_of_supportedIn RelEffCartierDiv.nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn Scheme.Modules.pullbackTensorObjIso RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.IdealSheafData.comap_mul Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso algEquivZeroCut RigidifiedLineBundle.pullbackAlongPullbackAlongIso relSubPicPresheaf fibreModule exists_relEffCartierDiv_supportedIn_rigidify_iso_of_subsingleton_H1_of_support_subset relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover exists_opens_range_subset_iff_forall_support_zeroSchemeIdeal_subset_of_forall_fibre"
namespace ChartE
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard NeronModelInfra"

theorem pullbackAlong_congr_hom {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') {φ₁ φ₂ : T ⟶ T'} (h : φ₁ = φ₂) (h₁ : φ₁ ≫ g' = g)
    (h₂ : φ₂ ≫ g' = g) : D.pullbackAlong φ₁ h₁ = D.pullbackAlong φ₂ h₂ := by
  subst h; rfl

theorem pullbackAlong_I_eq_mul {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n m l : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') (D₀ : RelEffCartierDiv f m g')
    (F : RelEffCartierDiv f l g') (hD : D.I = D₀.I * F.I) {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    (D.pullbackAlong φ hφ).I = (D₀.pullbackAlong φ hφ).I * (F.pullbackAlong φ hφ).I := by
  change D.I.comap _ = D₀.I.comap _ * F.I.comap _
  rw [hD, Scheme.IdealSheafData.comap_mul]

theorem OverTotal_snd_eq_of_eq {Cat : Type*} [Category Cat] {S : Cat} {G : (Over S)ᵒᵖ ⥤ Type*} {T : Cat}
    {a b : G.OverTotal T} (h : a = b) :
    b.2 = G.map (Over.homMk (𝟙 T) (by simp [h]) : Over.mk b.1 ⟶ Over.mk a.1).op a.2 := by
  subst h
  exact (Functor.map_op_apply_eq_self _ (by simp) _).symm

theorem RigidifiedLineBundle_pullbackAlong_L_eq {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) {ψ ψ' : SchemeHomOver t' t} (h : ψ.1 = ψ'.1) :
    (M.pullbackAlong ψ).L = (M.pullbackAlong ψ').L := by
  rw [Subtype.ext h]

abbrev FinerAt {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) : Prop :=
  ∀ σ : 𝟙_ (pullback c (s ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj M,
    σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (s ≫ t))) ⊆
      ((pullback.fst c (s ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫ t)))

theorem finerAt_congr_hom {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {k : Type u} [Field k] {s s' : Spec (CommRingCat.of k) ⟶ T} (h : s = s') :
    FinerAt c U t M s ↔ FinerAt c U t M s' := by
  subst h; exact Iff.rfl

theorem finerAt_congr_iso {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {M M' : (pullback c t).Modules} (i : M ≅ M')
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    FinerAt c U t M s ↔ FinerAt c U t M' s := by

  suffices key : ∀ {N N' : (pullback c t).Modules} (j : N ≅ N'), FinerAt c U t N s → FinerAt c U t N' s from
    ⟨key i, key i.symm⟩
  intro N N' j h σ' hσ'
  let F : (pullback c t).Modules ⥤ (pullback c (s ≫ t)).Modules := Scheme.Modules.pullback (mapOnProdOver c s rfl)
  have hσ : σ' ≫ F.map j.inv ≠ 0 := by
    intro h0
    apply hσ'
    have := congrArg (· ≫ F.map j.hom) h0
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id,
      Limits.zero_comp] at this
    exact this
  have hZ : Scheme.Modules.zeroSchemeIdeal (σ' ≫ F.map j.inv) = Scheme.Modules.zeroSchemeIdeal σ' :=
    Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso σ' (F.map j.inv)
  simpa only [hZ] using h (σ' ≫ F.map j.inv) hσ

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {ρ : ℕ} (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)

omit [IsSeparated c] [SmoothOfRelativeDimension 1 (U.ι ≫ c)] in
@[reassoc (attr := simp)]
theorem rigSection_snd' {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    rigSection c u ε ≫ pullback.snd c u = 𝟙 V :=
  pullback.lift_snd _ _ _

include hEU in

theorem isInvertible_EI {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (E.pullbackAlong u (Category.comp_id u)).I.IsInvertible :=
  (E.pullbackAlong u (Category.comp_id u)).isInvertible_I_of_supportedIn U (hEU.pullbackAlong u (Category.comp_id u))

noncomputable abbrev Mγ {e : ℕ} (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) {V : Scheme.{u}}
    (u : V ⟶ Spec (CommRingCat.of R)) (LV : RigidifiedLineBundle c ε u) : (pullback c u).Modules :=
  LV.L ⊗ ((E.pullbackAlong u (Category.comp_id u)).lineBundle ⊗ (Dγ.pullbackAlong u (Category.comp_id u)).idealModule)

theorem isInvertible_Dγ {e : ℕ} (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
    {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (Dγ.pullbackAlong u (Category.comp_id u)).I.IsInvertible :=
  RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hDγ.pullbackAlong u (Category.comp_id u))

include hEU in
theorem isInvertible_Mγ {e : ℕ} (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
    {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) (LV : RigidifiedLineBundle c ε u) :
    Scheme.Modules.IsInvertible (Mγ R c ε E Dγ u LV) :=
  LV.isInvertible.tensor ((isInvertible_EI R c U E hEU u).isInvertible_invModule.tensor
    (isInvertible_Dγ R c U Dγ hDγ u).isInvertible_module)

section Transport

variable {e : ℕ} (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
  {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
  (ψ : SchemeHomOver t' t) (L : RigidifiedLineBundle c ε t)
  {k : Type u} [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')

noncomputable def fibreIso : pullback (pullback.snd c t) (s' ≫ ψ.1) ≅ pullback (pullback.snd c t') s' :=
  pullbackLeftPullbackSndIso c t (s' ≫ ψ.1) ≪≫
    pullback.congrHom rfl (by rw [Category.assoc, ψ.2]) ≪≫ (pullbackLeftPullbackSndIso c t' s').symm

omit [IsSeparated c] in
theorem fibreIso_hom_fibreAt :
    (fibreIso R c t t' ψ s').hom ≫ fibreAt c t' s' = fibreAt c t (s' ≫ ψ.1) := by
  simp only [fibreIso, fibreAt, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

omit [IsSeparated c] in
theorem fibreIso_hom_fst_baseChangeSnd :
    (fibreIso R c t t' ψ s').hom ≫ pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ =
      pullback.fst (pullback.snd c t) (s' ≫ ψ.1) := by
  have hβ : baseChangeSnd c ψ =
      pullback.lift (pullback.fst c t' ≫ 𝟙 C) (pullback.snd c t' ≫ ψ.1)
        (by simp [ψ.2, pullback.condition]) := rfl
  rw [hβ]
  apply pullback.hom_ext
  · simp only [fibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_fst, Category.comp_id,
      pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullbackLeftPullbackSndIso_hom_fst]
  · simp only [fibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      pullbackLeftPullbackSndIso_inv_fst_snd_assoc, pullback.congrHom_hom,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]

include hEU hDγ in

theorem nonempty_Mγ_iso_pullback :
    Nonempty (Mγ R c ε E Dγ t' (L.pullbackAlong ψ) ≅
      (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (Mγ R c ε E Dγ t L)) := by
  have hcomp : (Dγ.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ.1 ψ.2 =
      Dγ.pullbackAlong t' (Category.comp_id _) :=
    (RelEffCartierDiv.pullbackAlong_comp _ _ _ _ _).trans
      (pullbackAlong_congr_hom Dγ ψ.2 _ _)
  have hI : (Dγ.pullbackAlong t' (Category.comp_id _)).I =
      (Dγ.pullbackAlong t (Category.comp_id t)).I.comap (baseChangeSnd c ψ) := by
    rw [← hcomp]; rfl
  have iγ : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (Dγ.pullbackAlong t (Category.comp_id t)).idealModule ≅
      (Dγ.pullbackAlong t' (Category.comp_id _)).idealModule := by
    haveI := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison (baseChangeSnd c ψ)
      (isInvertible_Dγ R c U Dγ hDγ t)
      (hI ▸ isInvertible_Dγ R c U Dγ hDγ t')
    exact asIso ((Dγ.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison (baseChangeSnd c ψ)) ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hI).symm
  have iE := (RelEffCartierDiv.nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn R c U E hEU ψ).some
  exact ⟨(Iso.refl _ ⊗ᵢ (iE.symm ⊗ᵢ iγ.symm)) ≪≫
      (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm⟩

include hEU hDγ in

theorem nonempty_fibreModule_iso :
    Nonempty (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε E Dγ t L) ≅
      (Scheme.Modules.pullback (fibreIso R c t t' ψ s').hom).obj
        (fibreModule c t' s' (Mγ R c ε E Dγ t' (L.pullbackAlong ψ)))) := by
  obtain ⟨iM⟩ := nonempty_Mγ_iso_pullback R c ε U E hEU Dγ hDγ t t' ψ L
  exact ⟨((Scheme.Modules.pullbackCongr (fibreIso_hom_fst_baseChangeSnd R c t t' ψ s')).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso R c t t' ψ s').hom
      (pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ)).app _).symm ≪≫
    (Scheme.Modules.pullback (fibreIso R c t t' ψ s').hom).mapIso
      (((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd c t') s') (baseChangeSnd c ψ)).app _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso iM.symm)⟩

include hEU hDγ in

theorem fibre_transport_to_t (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε E Dγ t L))).H1 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s' (Mγ R c ε E Dγ t' (L.pullbackAlong ψ)))).H1) := by
  obtain ⟨eφ⟩ := nonempty_fibreModule_iso R c ε U E hEU Dγ hDγ t t' ψ L s'
  obtain ⟨𝒱, -, -, -, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (s' ≫ ψ.1)) (fibreAt c t' s') (fibreIso R c t t' ψ s') (fibreIso_hom_fibreAt R c t t' ψ s') 𝒲 _ _ eφ
  exact ⟨𝒱, h1⟩

include hEU hDγ in

theorem fibre_transport_to_t' (𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback (pullback.snd c t') s').TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf (fibreAt c t' s') (fibreModule c t' s' (Mγ R c ε E Dγ t' (L.pullbackAlong ψ)))).H1 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε E Dγ t L))).H1) := by
  obtain ⟨eφ⟩ := nonempty_fibreModule_iso R c ε U E hEU Dγ hDγ t t' ψ L s'
  let φ := fibreIso R c t t' ψ s'
  have hφ' : φ.symm.hom ≫ fibreAt c t (s' ≫ ψ.1) = fibreAt c t' s' := by
    rw [Iso.symm_hom, Iso.inv_comp_eq, fibreIso_hom_fibreAt]
  have e' := ((Scheme.Modules.pullbackId _).app _).symm ≪≫
    ((Scheme.Modules.pullbackCongr φ.inv_hom_id).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app _).symm ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso eφ.symm
  obtain ⟨𝒱, -, -, -, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t' s') (fibreAt c t (s' ≫ ψ.1)) φ.symm hφ' 𝒲 _ _ e'
  exact ⟨𝒱, h1⟩

include hEU hDγ in

theorem forall_subsingleton_H1_pullbackAlong
    (h : ∀ 𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε E Dγ t L))).H1)
    (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s' (Mγ R c ε E Dγ t' (L.pullbackAlong ψ)))).H1 := by
  obtain ⟨𝒱, ⟨e1⟩⟩ := fibre_transport_to_t R c ε U E hEU Dγ hDγ t t' ψ L s' 𝒲
  haveI := h 𝒱
  exact e1.symm.toEquiv.subsingleton

include hEU hDγ in

theorem forall_subsingleton_H1_of_pullbackAlong
    (h : ∀ 𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s' (Mγ R c ε E Dγ t' (L.pullbackAlong ψ)))).H1)
    (𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε E Dγ t L))).H1 := by
  obtain ⟨𝒱, ⟨e1⟩⟩ := fibre_transport_to_t' R c ε U E hEU Dγ hDγ t t' ψ L s' 𝒲
  haveI := h 𝒱
  exact e1.symm.toEquiv.subsingleton

omit [IsSeparated c] [SmoothOfRelativeDimension 1 (U.ι ≫ c)] in

private theorem _root_.AlgebraicGeometry.RelPicard.ChartE.finerAt_transport (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M) (M' : (pullback c t').Modules)
    (i : M' ≅ (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj M) :
    FinerAt c U t' M' s' ↔ FinerAt c U t M (s' ≫ ψ.1) :=
  AlgebraicGeometry.RelPicard.FinTransport.finerAt_transport c U t t' ψ M hM M' i s'

p2m_export "AlgebraicGeometry.RelPicard.ChartE" "finerAt_transport"
include hEU hDγ in

theorem finerAt_Mγ_pullbackAlong_iff :
    FinerAt c U t' (Mγ R c ε E Dγ t' (L.pullbackAlong ψ)) s' ↔ FinerAt c U t (Mγ R c ε E Dγ t L) (s' ≫ ψ.1) :=
  finerAt_transport R c U t t' ψ s' _ (isInvertible_Mγ R c ε U E hEU Dγ hDγ t L) _
    (nonempty_Mγ_iso_pullback R c ε U E hEU Dγ hDγ t t' ψ L).some

end Transport
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard.FinTransport"

omit [IsSeparated c] in

theorem forall_subsingleton_H1_of_iso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {F F' : (pullback c t).Modules} (i : F ≅ F') {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (h : ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F')).H1 := by
  have e : fibreModule c t s F ≅ (Scheme.Modules.pullback (Iso.refl (pullback (pullback.snd c t) s)).hom).obj
      (fibreModule c t s F') :=
    (Scheme.Modules.pullback _).mapIso i ≪≫ ((Scheme.Modules.pullbackId _).app _).symm
  obtain ⟨𝒱, -, -, -, ⟨h1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) (fibreAt c t s) (Iso.refl _) (Category.id_comp _) 𝒲 _ _ e
  haveI := h 𝒱
  exact h1.symm.toEquiv.subsingleton

section Chart

set_option linter.unusedSectionVars false

section Generic
omit [IsSeparated c] [SmoothOfRelativeDimension 1 (U.ι ≫ c)]

theorem uliftYonedaEquiv_uliftYoneda_map_comp {F : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)} {T T' : Scheme.{u}} (ψ : T' ⟶ T)
    (f : uliftYoneda.{u + 1}.obj T ⟶ F) :
    uliftYonedaEquiv.{u + 1, u, u + 1} (uliftYoneda.{u + 1}.map ψ ≫ f) =
      F.map ψ.op (uliftYonedaEquiv.{u + 1, u, u + 1} f) :=
  (uliftYonedaEquiv_naturality f ψ.op).symm

noncomputable def pointElem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t)
    (hL : FibrewiseAlgEquivZero L) :
    (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal.obj (op T) :=
  ⟨t, ⟨Quotient.mk _ L, hL⟩⟩

@[scoped simp] theorem pointElem_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t)
    (hL : FibrewiseAlgEquivZero L) : (pointElem R c ε t L hL).1 = t := rfl

theorem forall_subsingleton_H1_congr_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (F : (pullback c t).Modules)
    {k : Type u} [Field k] {s s' : Spec (CommRingCat.of k) ⟶ T} (h : s = s') :
    (∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1) ↔
    (∀ 𝒲 : (pullback (pullback.snd c t) s').TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t s') (fibreModule c t s' F)).H1) := by
  subst h; exact Iff.rfl

end Generic
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard.FinTransport"

variable [IsNoetherianRing R] [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
  (g e : ℕ) (hr : g + e = ρ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
  (hsect : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType u] (M : (pullback c u).Modules),
      Scheme.Modules.IsInvertible M →
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ V) (𝒲 : (pullback (pullback.snd c u) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H0 = 1) →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ V)
        (σ : 𝟙_ (pullback c (x ≫ u)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ u), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) →
      ∃ (D₀ : RelEffCartierDiv c g u) (N : V.Modules), Scheme.Modules.IsInvertible N ∧
        Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N) ∧
        ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' u) (N' : V.Modules), Scheme.Modules.IsInvertible N' → D'.SupportedIn U →
          Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N') → D'.I = D₀.I)
  (hZfibγ : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →
        ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ t))) ⊆ ((pullback.fst c (x ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ t))) →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)
  (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)
  (havoid : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))),
        σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ t))) ⊆ ((pullback.fst c (x ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ t)))) →
      ∀ (D₀ : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N →
        Nonempty (D₀.lineBundle ≅
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ⊗
            (Scheme.Modules.pullback (pullback.snd c t)).obj N) →
        D₀.SupportedIn U)

include 𝒱 hr hEU hDγ hH0one

theorem exists_finerOpen {V : Scheme.{u}} (v : V ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType v]
    (LV : RigidifiedLineBundle c ε v) (hLV : FibrewiseAlgEquivZero LV) :
    ∃ W' : V.Opens, ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ V),
      Set.range ⇑s ⊆ (W' : Set V) ↔
        (∀ 𝒲 : (pullback (pullback.snd c v) s).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (fibreAt c v s) (fibreModule c v s (Mγ R c ε E Dγ v LV))).H1) ∧
        FinerAt c U v (Mγ R c ε E Dγ v LV) s := by

  obtain ⟨W, hW⟩ := exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover R c 𝒱 v
    (Mγ R c ε E Dγ v LV) (isInvertible_Mγ R c ε U E hEU Dγ hDγ v LV)

  let ι : SchemeHomOver (W.ι ≫ v) v := ⟨W.ι, rfl⟩
  have hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u}))
      (𝒲 : (pullback (pullback.snd c (W.ι ≫ v)) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c (W.ι ≫ v) s) (fibreModule c (W.ι ≫ v) s
        (Mγ R c ε E Dγ (W.ι ≫ v) (LV.pullbackAlong ι)))).H1 ∧
      Module.finrank k (𝒲.sectionsOf (fibreAt c (W.ι ≫ v) s) (fibreModule c (W.ι ≫ v) s
        (Mγ R c ε E Dγ (W.ι ≫ v) (LV.pullbackAlong ι)))).H0 = 1 := by
    intro k _ s 𝒲
    have hrange : Set.range ⇑(s ≫ ι.1) ⊆ (W : Set V) := by
      rintro _ ⟨x, rfl⟩
      change (s ≫ W.ι) x ∈ (W : Set V)
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact (s x).2
    have h1 := forall_subsingleton_H1_pullbackAlong R c ε U E hEU Dγ hDγ v (W.ι ≫ v) ι LV s ((hW k (s ≫ ι.1)).1 hrange)
    exact ⟨h1 𝒲, hH0one (W.ι ≫ v) (LV.pullbackAlong ι) (hLV.pullback ι) k s 𝒲 (h1 𝒲)⟩

  obtain ⟨A, hA⟩ := exists_opens_range_subset_iff_forall_support_zeroSchemeIdeal_subset_of_forall_fibre R c 𝒱 U (W.ι ≫ v)
    (Mγ R c ε E Dγ (W.ι ≫ v) (LV.pullbackAlong ι)) (isInvertible_Mγ R c ε U E hEU Dγ hDγ _ _) hfib
  refine ⟨W.ι ''ᵁ A, fun k _ s => ?_⟩

  have lift_through : Set.range ⇑s ⊆ (W : Set V) → ∃ s₀ : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u}), s₀ ≫ W.ι = s := fun hsW =>
    ⟨IsOpenImmersion.lift W.ι s (by rwa [Scheme.Opens.range_ι]), IsOpenImmersion.lift_fac _ _ _⟩
  constructor
  · intro hs
    have hsW : Set.range ⇑s ⊆ (W : Set V) := hs.trans (Scheme.Opens.ι_image_le W A)
    obtain ⟨s₀, hs₀⟩ := lift_through hsW
    have hA₀ : Set.range ⇑s₀ ⊆ (A : Set W) := by
      rintro _ ⟨x, rfl⟩
      have hx : (W.ι (s₀ x) : V) ∈ W.ι ''ᵁ A := by
        rw [← Scheme.Hom.comp_apply, hs₀]; exact hs ⟨x, rfl⟩
      exact (Scheme.Hom.apply_mem_image_iff W.ι).1 hx
    refine ⟨(hW k s).1 hsW, ?_⟩
    have hfin := (finerAt_Mγ_pullbackAlong_iff R c ε U E hEU Dγ hDγ v (W.ι ≫ v) ι LV s₀).1 ((hA k s₀).1 hA₀)
    exact (finerAt_congr_hom c U v _ hs₀).1 hfin
  · rintro ⟨hH1, hfin⟩
    obtain ⟨s₀, hs₀⟩ := lift_through ((hW k s).2 hH1)
    have hA₀ : Set.range ⇑s₀ ⊆ (A : Set W) :=
      (hA k s₀).2 ((finerAt_Mγ_pullbackAlong_iff R c ε U E hEU Dγ hDγ v (W.ι ≫ v) ι LV s₀).2
        ((finerAt_congr_hom c U v _ hs₀).2 hfin))
    rintro _ ⟨x, rfl⟩
    rw [← hs₀, Scheme.Hom.comp_apply]
    exact (Scheme.Hom.apply_mem_image_iff W.ι).2 (hA₀ ⟨x, rfl⟩)

variable {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType y] (𝒟 : RelEffCartierDiv c g y) (h𝒟U : 𝒟.SupportedIn U)
  (huniv : ∀ ⦃T : Scheme.{u}⦄ (g' : T ⟶ Spec (CommRingCat.of R)) (D : RelEffCartierDiv c g g'), D.SupportedIn U →
    ∃! φ : {φ : T ⟶ Y // φ ≫ y = g'}, PullsBackOver 𝒟 φ.1 φ.2 D)
  (DY : RelEffCartierDiv c ρ y) (hDY : DY.I = 𝒟.I * (Dγ.pullbackAlong y (Category.comp_id y)).I) (hDYU : DY.SupportedIn U)

noncomputable def LY : RigidifiedLineBundle c ε y :=
  ⟨Scheme.Modules.rigidify (rigSection c y ε) (pullback.snd c y)
      (DY.lineBundle ⊗ (E.pullbackAlong y (Category.comp_id y)).idealModule),
    (RelEffCartierDiv.isInvertible_rigidify_lineBundle_tensor_idealModule_and_nonempty_pullback_iso_of_supportedIn
      c ε U E hEU DY hDYU).1,
    (RelEffCartierDiv.isInvertible_rigidify_lineBundle_tensor_idealModule_and_nonempty_pullback_iso_of_supportedIn
      c ε U E hEU DY hDYU).2⟩

omit [IsNoetherianRing R] [IsProper c] [Flat c] hDγ hH0one 𝒱 hr in
@[scoped simp] theorem LY_L : (LY R c ε U E hEU y DY hDYU).L =
    Scheme.Modules.rigidify (rigSection c y ε) (pullback.snd c y)
      (DY.lineBundle ⊗ (E.pullbackAlong y (Category.comp_id y)).idealModule) := rfl

section HunivAPI
omit [IsSeparated c] [SmoothOfRelativeDimension 1 (U.ι ≫ c)] [IsNoetherianRing R] [IsProper c] [Flat c] [LocallyOfFiniteType y]
  hEU hDγ hH0one 𝒱 hr

variable {T₁ : Scheme.{u}} {g₁ : T₁ ⟶ Spec (CommRingCat.of R)} (D₁ : RelEffCartierDiv c g g₁) (hD₁ : D₁.SupportedIn U)

noncomputable def hulift : T₁ ⟶ Y := ((huniv g₁ D₁ hD₁).exists.choose).1

theorem hulift_comp : hulift R c U g y 𝒟 huniv D₁ hD₁ ≫ y = g₁ := ((huniv g₁ D₁ hD₁).exists.choose).2

theorem pullsBackOver_hulift : PullsBackOver 𝒟 (hulift R c U g y 𝒟 huniv D₁ hD₁) (hulift_comp R c U g y 𝒟 huniv D₁ hD₁) D₁ :=
  (huniv g₁ D₁ hD₁).exists.choose_spec

theorem pullbackAlong_hulift :
    𝒟.pullbackAlong (hulift R c U g y 𝒟 huniv D₁ hD₁) (hulift_comp R c U g y 𝒟 huniv D₁ hD₁) = D₁ :=
  (PullsBackOver.eq_pullbackAlong (pullsBackOver_hulift R c U g y 𝒟 huniv D₁ hD₁)).symm

theorem eq_hulift {φ : T₁ ⟶ Y} (hφ : φ ≫ y = g₁) (h : PullsBackOver 𝒟 φ hφ D₁) :
    φ = hulift R c U g y 𝒟 huniv D₁ hD₁ := by
  have := (huniv g₁ D₁ hD₁).unique (y₁ := ⟨φ, hφ⟩) (y₂ := (huniv g₁ D₁ hD₁).exists.choose) h
    (huniv g₁ D₁ hD₁).exists.choose_spec
  exact congrArg Subtype.val this

end HunivAPI
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard.FinTransport"

variable

  (WY : Y.Opens)
  (hWY : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Y),
    Set.range ⇑s ⊆ (WY : Set Y) ↔
      IsAlgEquivZero (fibreAt c y s) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c y) s)).obj
        (Scheme.Modules.rigidify (rigSection c y ε) (pullback.snd c y)
          (DY.lineBundle ⊗ (E.pullbackAlong y (Category.comp_id y)).idealModule))))

include hsect hZfibγ h𝒟U huniv hDY hDYU hWY

theorem fibrewiseAlgEquivZero_LY_WY :
    FibrewiseAlgEquivZero ((LY R c ε U E hEU y DY hDYU).pullbackAlong
      (⟨WY.ι, rfl⟩ : SchemeHomOver (WY.ι ≫ y) y)) := by
  intro k _ _ s'
  set ψ : SchemeHomOver (WY.ι ≫ y) y := ⟨WY.ι, rfl⟩ with hψ
  let φ := fibreIso R c y (WY.ι ≫ y) ψ s'
  have hrange : Set.range ⇑(s' ≫ ψ.1) ⊆ (WY : Set Y) := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    exact (s' z).2
  have h0 := (hWY k (s' ≫ ψ.1)).1 hrange
  have he : φ.inv ≫ fibreAt c y (s' ≫ ψ.1) = fibreAt c (WY.ι ≫ y) s' := by
    rw [Iso.inv_comp_eq]
    exact (fibreIso_hom_fibreAt R c y (WY.ι ≫ y) ψ s').symm
  have h1 := h0.pullback φ.inv he
  have hfst : φ.inv ≫ pullback.fst (pullback.snd c y) (s' ≫ ψ.1) =
      pullback.fst (pullback.snd c (WY.ι ≫ y)) s' ≫ baseChangeSnd c ψ := by
    rw [Iso.inv_comp_eq]
    exact (fibreIso_hom_fst_baseChangeSnd R c y (WY.ι ≫ y) ψ s').symm
  refine IsAlgEquivZero.of_iso ?_ h1
  exact (Scheme.Modules.pullbackComp φ.inv (pullback.fst (pullback.snd c y) (s' ≫ ψ.1))).app _ ≪≫
    (Scheme.Modules.pullbackCongr hfst).app _ ≪≫
    ((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd c (WY.ι ≫ y)) s') (baseChangeSnd c ψ)).app _).symm

variable

  (X : (WY : Scheme.{u}).Opens)
  (hX : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (WY : Scheme.{u})),
    Set.range ⇑s ⊆ (X : Set WY) ↔
      (∀ 𝒲 : (pullback (pullback.snd c (WY.ι ≫ y)) s).TwoAffineOpenCover,
        Subsingleton (𝒲.sectionsOf (fibreAt c (WY.ι ≫ y) s) (fibreModule c (WY.ι ≫ y) s
          (Mγ R c ε E Dγ (WY.ι ≫ y) ((LY R c ε U E hEU y DY hDYU).pullbackAlong (⟨WY.ι, rfl⟩ : SchemeHomOver (WY.ι ≫ y) y))))).H1) ∧
      FinerAt c U (WY.ι ≫ y) (Mγ R c ε E Dγ (WY.ι ≫ y) ((LY R c ε U E hEU y DY hDYU).pullbackAlong (⟨WY.ι, rfl⟩ : SchemeHomOver (WY.ι ≫ y) y))) s)

include hX

noncomputable abbrev jX : (X : Scheme.{u}) ⟶ Y := X.ι ≫ WY.ι

theorem fibrewiseAlgEquivZero_LY_X :
    FibrewiseAlgEquivZero ((LY R c ε U E hEU y DY hDYU).pullbackAlong
      (⟨jX WY X, rfl⟩ : SchemeHomOver (jX WY X ≫ y) y)) := by
  have h := (fibrewiseAlgEquivZero_LY_WY R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY).pullback
    (⟨X.ι, rfl⟩ : SchemeHomOver (X.ι ≫ WY.ι ≫ y) (WY.ι ≫ y))
  refine (h.congr ⟨RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
    eqToIso (RigidifiedLineBundle_pullbackAlong_L_eq _ ?_)⟩)
  rfl

noncomputable def chartElem :
    (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal.obj (op (X : Scheme.{u})) :=
  ⟨jX WY X ≫ y, ⟨Quotient.mk _ ((LY R c ε U E hEU y DY hDYU).pullbackAlong (⟨jX WY X, rfl⟩ : SchemeHomOver (jX WY X ≫ y) y)),
    fibrewiseAlgEquivZero_LY_X R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX⟩⟩

@[scoped simp] theorem chartElem_fst :
    (chartElem R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX).1 = jX WY X ≫ y := rfl

noncomputable def chartMap :
    uliftYoneda.{u + 1}.obj (X : Scheme.{u}) ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal :=
  uliftYonedaEquiv.{u + 1, u, u + 1}.symm
    (chartElem R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX)

@[scoped simp] theorem uliftYonedaEquiv_chartMap :
    uliftYonedaEquiv.{u + 1, u, u + 1} (chartMap R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX) =
      chartElem R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX :=
  Equiv.apply_symm_apply _ _

theorem uliftYonedaEquiv_map_comp_chartMap {T : Scheme.{u}} (φ' : T ⟶ (X : Scheme.{u})) :
    uliftYonedaEquiv.{u + 1, u, u + 1} (uliftYoneda.{u + 1}.map φ' ≫
        chartMap R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX) =
      (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal.map φ'.op
        (chartElem R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX) := by
  rw [uliftYonedaEquiv_uliftYoneda_map_comp, uliftYonedaEquiv_chartMap]

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t] (L : RigidifiedLineBundle c ε t)
  (hL : FibrewiseAlgEquivZero L) (W : T.Opens)
  (hWiff : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
    Set.range ⇑s ⊆ (W : Set T) ↔
      (∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (Mγ R c ε E Dγ t L))).H1) ∧
      FinerAt c U t (Mγ R c ε E Dγ t L) s)
  (D : RelEffCartierDiv c ρ (W.ι ≫ t)) (D₀ : RelEffCartierDiv c g (W.ι ≫ t))
  (hD : D.I = D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I)
  (hDL : Nonempty (Scheme.Modules.rigidify (rigSection c (W.ι ≫ t) ε) (pullback.snd c (W.ι ≫ t))
      (D.lineBundle ⊗ (E.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).idealModule) ≅
    (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L))
  (hD₀U : D₀.SupportedIn U)

include hL hWiff hD hDL hD₀U

theorem D_eq_pullbackAlong_lift :
    D = DY.pullbackAlong (hulift R c U g y 𝒟 huniv D₀ hD₀U) (hulift_comp R c U g y 𝒟 huniv D₀ hD₀U) := by
  refine RelEffCartierDiv.ext ?_
  rw [pullbackAlong_I_eq_mul DY 𝒟 _ hDY, pullbackAlong_hulift R c U g y 𝒟 huniv D₀ hD₀U, RelEffCartierDiv.pullbackAlong_comp,
    pullbackAlong_congr_hom Dγ (hulift_comp R c U g y 𝒟 huniv D₀ hD₀U) _ (Category.comp_id _)]
  exact hD

noncomputable abbrev φ₀ : SchemeHomOver (W.ι ≫ t) y :=
  ⟨hulift R c U g y 𝒟 huniv D₀ hD₀U, hulift_comp R c U g y 𝒟 huniv D₀ hD₀U⟩

theorem nonempty_LY_pullbackAlong_lift_iso :
    Nonempty (((LY R c ε U E hEU y DY hDYU).pullbackAlong (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U)).L ≅
      (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L) := by
  obtain ⟨i⟩ := RelEffCartierDiv.nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn
    c ε U E hEU (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U) DY hDYU
  refine ⟨i.symm ≪≫ eqToIso (congrArg (fun D' : RelEffCartierDiv c ρ (W.ι ≫ t) =>
      Scheme.Modules.rigidify (rigSection c (W.ι ≫ t) ε) (pullback.snd c (W.ι ≫ t))
        (D'.lineBundle ⊗ (E.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).idealModule))
    (D_eq_pullbackAlong_lift R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U).symm) ≪≫ hDL.some⟩

theorem nonempty_Mγ_LY_pullbackAlong_lift_iso :
    Nonempty (Mγ R c ε E Dγ (W.ι ≫ t) ((LY R c ε U E hEU y DY hDYU).pullbackAlong (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U)) ≅
      Mγ R c ε E Dγ (W.ι ≫ t) (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t))) :=
  ⟨(nonempty_LY_pullbackAlong_lift_iso R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U).some ⊗ᵢ Iso.refl _⟩

theorem subsingleton_H1_W (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u}))
    (𝒲 : (pullback (pullback.snd c (W.ι ≫ t)) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c (W.ι ≫ t) s) (fibreModule c (W.ι ≫ t) s
      (Mγ R c ε E Dγ (W.ι ≫ t) (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t))))).H1 := by
  have hrange : Set.range ⇑(s ≫ W.ι) ⊆ (W : Set T) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    exact (s x).2
  exact forall_subsingleton_H1_pullbackAlong R c ε U E hEU Dγ hDγ t (W.ι ≫ t) ⟨W.ι, rfl⟩ L s
    ((hWiff k (s ≫ W.ι)).1 hrange).1 𝒲

theorem subsingleton_H1_W' (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u}))
    (𝒲 : (pullback (pullback.snd c (W.ι ≫ t)) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c (W.ι ≫ t) s) (fibreModule c (W.ι ≫ t) s
      (Mγ R c ε E Dγ (W.ι ≫ t)
        ((LY R c ε U E hEU y DY hDYU).pullbackAlong (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U))))).H1 := by
  obtain ⟨i⟩ := nonempty_Mγ_LY_pullbackAlong_lift_iso R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U
  exact forall_subsingleton_H1_of_iso R c (W.ι ≫ t) i.symm s
    (subsingleton_H1_W R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U k s) 𝒲

theorem finerAt_W' (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u})) :
    FinerAt c U (W.ι ≫ t) (Mγ R c ε E Dγ (W.ι ≫ t)
      ((LY R c ε U E hEU y DY hDYU).pullbackAlong (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U))) s := by
  have hrange : Set.range ⇑(s ≫ W.ι) ⊆ (W : Set T) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    exact (s x).2
  have h := ((hWiff k (s ≫ W.ι)).1 hrange).2
  have h' := (finerAt_Mγ_pullbackAlong_iff R c ε U E hEU Dγ hDγ t (W.ι ≫ t) ⟨W.ι, rfl⟩ L s).2 h
  obtain ⟨i⟩ := nonempty_Mγ_LY_pullbackAlong_lift_iso R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U
  exact (finerAt_congr_iso c U (W.ι ≫ t) i s).2 h'

theorem H1_and_finerAt_Y (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u})) :
    (∀ 𝒲 : (pullback (pullback.snd c y) (s ≫ hulift R c U g y 𝒟 huniv D₀ hD₀U)).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c y (s ≫ hulift R c U g y 𝒟 huniv D₀ hD₀U))
        (fibreModule c y (s ≫ hulift R c U g y 𝒟 huniv D₀ hD₀U) (Mγ R c ε E Dγ y (LY R c ε U E hEU y DY hDYU)))).H1) ∧
    FinerAt c U y (Mγ R c ε E Dγ y (LY R c ε U E hEU y DY hDYU)) (s ≫ hulift R c U g y 𝒟 huniv D₀ hD₀U) :=
  ⟨forall_subsingleton_H1_of_pullbackAlong R c ε U E hEU Dγ hDγ y (W.ι ≫ t) (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U)
      (LY R c ε U E hEU y DY hDYU) s (subsingleton_H1_W' R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U k s),
    (finerAt_Mγ_pullbackAlong_iff R c ε U E hEU Dγ hDγ y (W.ι ≫ t) (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U)
      (LY R c ε U E hEU y DY hDYU) s).1 (finerAt_W' R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U k s)⟩

theorem range_lift_subset_WY : Set.range ⇑(hulift R c U g y 𝒟 huniv D₀ hD₀U) ⊆ (WY : Set Y) := by
  rintro _ ⟨p, rfl⟩
  classical

  let κ := (W : Scheme.{u}).residueField p
  let kb : Type u := AlgebraicClosure κ
  set sb : Spec (CommRingCat.of kb) ⟶ (W : Scheme.{u}) :=
    Spec.map (CommRingCat.ofHom (algebraMap κ kb)) ≫ (W : Scheme.{u}).fromSpecResidueField p with hsbdef
  have hsb : sb (IsLocalRing.closedPoint kb) = p := by
    change ((W : Scheme.{u}).fromSpecResidueField p) (Spec.map (CommRingCat.ofHom (algebraMap κ kb)) (IsLocalRing.closedPoint kb)) = p
    rw [show (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) (IsLocalRing.closedPoint kb) = IsLocalRing.closedPoint κ from
      Subsingleton.elim _ _, Scheme.fromSpecResidueField_apply]

  have hLW : FibrewiseAlgEquivZero (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)) := hL.pullback _
  have hLY : FibrewiseAlgEquivZero ((LY R c ε U E hEU y DY hDYU).pullbackAlong (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U)) :=
    hLW.congr ⟨(nonempty_LY_pullbackAlong_lift_iso R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U).some.symm⟩
  have h1 := hLY kb sb

  have key : IsAlgEquivZero (fibreAt c y (sb ≫ (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U).1))
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c y) (sb ≫ (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U).1))).obj
        (LY R c ε U E hEU y DY hDYU).L) := by
    have hψ' : pullback.snd c (W.ι ≫ t) ≫ (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U).1 =
        baseChangeSnd c (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U) ≫ pullback.snd c y := by
      simp only [baseChangeSnd, pullback.lift_snd]
    have hbC : baseChangeSnd c (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U) ≫ pullback.fst c y = pullback.fst c (W.ι ≫ t) := by
      simp only [baseChangeSnd, pullback.lift_fst, Category.comp_id]
    have H₁ : IsPullback (pullback.fst (pullback.snd c (W.ι ≫ t)) sb ≫ pullback.fst c (W.ι ≫ t))
        (pullback.snd (pullback.snd c (W.ι ≫ t)) sb) c (sb ≫ W.ι ≫ t) :=
      (IsPullback.of_hasPullback (pullback.snd c (W.ι ≫ t)) sb).paste_horiz (IsPullback.of_hasPullback c (W.ι ≫ t))
    have H₂ : IsPullback (pullback.fst (pullback.snd c y) (sb ≫ (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U).1) ≫ pullback.fst c y)
        (pullback.snd (pullback.snd c y) (sb ≫ (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U).1)) c (sb ≫ W.ι ≫ t) := by
      have := (IsPullback.of_hasPullback (pullback.snd c y) (sb ≫ (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U).1)).paste_horiz
        (IsPullback.of_hasPullback c y)
      simpa only [Category.assoc, (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U).2] using this
    let eI := H₁.isoIsPullback _ _ H₂
    have he : eI.hom ≫ fibreAt c y (sb ≫ (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U).1) = fibreAt c (W.ι ≫ t) sb :=
      IsPullback.isoIsPullback_hom_snd _ _ H₁ H₂
    have hfst : eI.hom ≫ pullback.fst (pullback.snd c y) (sb ≫ (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U).1) =
        pullback.fst (pullback.snd c (W.ι ≫ t)) sb ≫ baseChangeSnd c (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U) := by
      apply pullback.hom_ext
      · simp only [Category.assoc, hbC]
        exact IsPullback.isoIsPullback_hom_fst _ _ H₁ H₂
      · have h2 := IsPullback.isoIsPullback_hom_snd _ _ H₁ H₂
        simp only [Category.assoc]
        rw [← hψ', pullback.condition_assoc, pullback.condition, ← Category.assoc, h2]
    have h2 : IsAlgEquivZero (fibreAt c (W.ι ≫ t) sb) ((Scheme.Modules.pullback eI.hom).obj
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd c y) (sb ≫ (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U).1))).obj
          (LY R c ε U E hEU y DY hDYU).L)) := by
      refine IsAlgEquivZero.of_iso ?_ h1
      exact ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hfst).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm).symm
    refine IsAlgEquivZero.of_iso ?_ (h2.pullback eI.inv (by rw [← he, eI.inv_hom_id_assoc]))
    exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr eI.inv_hom_id).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _
  have hrange := (hWY kb (sb ≫ (φ₀ R c U g y 𝒟 huniv t W D₀ hD₀U).1)).2 key
  exact hrange ⟨IsLocalRing.closedPoint kb, by rw [Scheme.Hom.comp_apply, hsb]⟩

noncomputable def φ₁ : (W : Scheme.{u}) ⟶ (WY : Scheme.{u}) :=
  IsOpenImmersion.lift WY.ι (hulift R c U g y 𝒟 huniv D₀ hD₀U)
    (by rw [Scheme.Opens.range_ι]; exact range_lift_subset_WY R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U)

@[reassoc (attr := simp)]
theorem φ₁_ι : φ₁ R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U ≫ WY.ι = hulift R c U g y 𝒟 huniv D₀ hD₀U :=
  IsOpenImmersion.lift_fac _ _ _

theorem range_φ₁_subset_X : Set.range ⇑(φ₁ R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U) ⊆ (X : Set WY) := by
  rintro _ ⟨p, rfl⟩
  let s := (W : Scheme.{u}).fromSpecResidueField p
  have hs : (s ≫ φ₁ R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U) ≫ WY.ι = s ≫ hulift R c U g y 𝒟 huniv D₀ hD₀U := by
    rw [Category.assoc, φ₁_ι]
  obtain ⟨hH1, hfin⟩ := H1_and_finerAt_Y R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U _ s
  let ι : SchemeHomOver (WY.ι ≫ y) y := ⟨WY.ι, rfl⟩
  have key := (hX ((W : Scheme.{u}).residueField p) (s ≫ φ₁ R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U)).2
    ⟨forall_subsingleton_H1_pullbackAlong R c ε U E hEU Dγ hDγ y (WY.ι ≫ y) ι (LY R c ε U E hEU y DY hDYU) (s ≫ φ₁ R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U)
        ((forall_subsingleton_H1_congr_hom R c y _ hs).2 hH1),
      (finerAt_Mγ_pullbackAlong_iff R c ε U E hEU Dγ hDγ y (WY.ι ≫ y) ι (LY R c ε U E hEU y DY hDYU) (s ≫ φ₁ R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U)).2
        ((finerAt_congr_hom c U y _ hs).2 hfin)⟩
  refine key ⟨IsLocalRing.closedPoint _, ?_⟩
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

noncomputable def φ : (W : Scheme.{u}) ⟶ (X : Scheme.{u}) :=
  IsOpenImmersion.lift X.ι (φ₁ R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U)
    (by rw [Scheme.Opens.range_ι]; exact range_φ₁_subset_X R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U)

@[reassoc (attr := simp)]
theorem φ_jX : φ R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U ≫ jX WY X = hulift R c U g y 𝒟 huniv D₀ hD₀U := by
  rw [← Category.assoc, φ, IsOpenImmersion.lift_fac, φ₁_ι]

theorem clause_i (L' : RigidifiedLineBundle c ε t) (hL' : Nonempty (L'.L ≅ L.L))
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    Set.range ⇑s ⊆ (W : Set T) ↔
      (∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (Mγ R c ε E Dγ t L'))).H1) ∧
      FinerAt c U t (Mγ R c ε E Dγ t L') s := by
  have i : Mγ R c ε E Dγ t L ≅ Mγ R c ε E Dγ t L' := hL'.some.symm ⊗ᵢ Iso.refl _
  refine (hWiff k s).trans ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · exact forall_subsingleton_H1_of_iso R c t i s h.1
  · exact (finerAt_congr_iso c U t i s).1 h.2
  · exact forall_subsingleton_H1_of_iso R c t i.symm s h.1
  · exact (finerAt_congr_iso c U t i s).2 h.2

theorem clause_ii :
    uliftYoneda.{u + 1}.map (φ R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U) ≫ chartMap R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX =
      uliftYoneda.{u + 1}.map W.ι ≫ uliftYonedaEquiv.{u + 1, u, u + 1}.symm (pointElem R c ε t L hL) := by
  apply uliftYonedaEquiv.{u + 1, u, u + 1}.injective
  rw [uliftYonedaEquiv_map_comp_chartMap, uliftYonedaEquiv_uliftYoneda_map_comp, Equiv.apply_symm_apply]
  refine Functor.OverTotal.ext' ?_ ?_
  · change φ R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U ≫ jX WY X ≫ y = W.ι ≫ t
    rw [← Category.assoc, φ_jX, hulift_comp R c U g y 𝒟 huniv D₀ hD₀U]
  · apply Subtype.ext
    refine Quotient.sound ⟨?_⟩
    refine RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      eqToIso (RigidifiedLineBundle_pullbackAlong_L_eq _ ?_) ≪≫
      (nonempty_LY_pullbackAlong_lift_iso R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U).some
    simp [postComp]

theorem clause_iii {T' : Scheme.{u}} (ψ : T' ⟶ T) (φ' : T' ⟶ (X : Scheme.{u}))
    [LocallyOfFiniteType (ψ ≫ t)]
    (hφ' : uliftYoneda.{u + 1}.map φ' ≫ chartMap R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX =
      uliftYoneda.{u + 1}.map ψ ≫ uliftYonedaEquiv.{u + 1, u, u + 1}.symm (pointElem R c ε t L hL)) :
    ∃ χ : T' ⟶ (W : Scheme.{u}), χ ≫ W.ι = ψ ∧ χ ≫ φ R c ε U E hEU 𝒱 g e hr Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU WY hWY X hX t L hL W hWiff D D₀ hD hDL hD₀U = φ' := by

  have Eq := congrArg uliftYonedaEquiv.{u + 1, u, u + 1} hφ'
  rw [uliftYonedaEquiv_map_comp_chartMap, uliftYonedaEquiv_uliftYoneda_map_comp, Equiv.apply_symm_apply] at Eq
  have h1 : (φ' ≫ jX WY X) ≫ y = ψ ≫ t := by
    have := congrArg Sigma.fst Eq
    simpa [Functor.overTotal_map_fst] using this
  let Ψ : SchemeHomOver (ψ ≫ t) t := ⟨ψ, rfl⟩
  let Φ : SchemeHomOver (ψ ≫ t) y := ⟨φ' ≫ jX WY X, h1⟩

  have eL : Nonempty ((L.pullbackAlong Ψ).L ≅ ((LY R c ε U E hEU y DY hDYU).pullbackAlong Φ).L) := by
    have h2 := OverTotal_snd_eq_of_eq Eq
    obtain ⟨i⟩ := Quotient.exact (congrArg Subtype.val h2)
    exact ⟨i ≪≫ RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      eqToIso (RigidifiedLineBundle_pullbackAlong_L_eq _ (by simp [postComp, Φ]))⟩
  have eM : Mγ R c ε E Dγ (ψ ≫ t) ((LY R c ε U E hEU y DY hDYU).pullbackAlong Φ) ≅ Mγ R c ε E Dγ (ψ ≫ t) (L.pullbackAlong Ψ) :=
    eL.some.symm ⊗ᵢ Iso.refl _

  have hD' : (DY.pullbackAlong (φ' ≫ jX WY X) h1).I =
      (𝒟.pullbackAlong (φ' ≫ jX WY X) h1).I * (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).I := by
    rw [pullbackAlong_I_eq_mul DY 𝒟 _ hDY, RelEffCartierDiv.pullbackAlong_comp,
      pullbackAlong_congr_hom Dγ h1 _ (Category.comp_id _)]
  have hD'L : Nonempty (Scheme.Modules.rigidify (rigSection c (ψ ≫ t) ε) (pullback.snd c (ψ ≫ t))
      ((DY.pullbackAlong (φ' ≫ jX WY X) h1).lineBundle ⊗ (E.pullbackAlong (ψ ≫ t) (Category.comp_id _)).idealModule) ≅
        (L.pullbackAlong Ψ).L) := by
    obtain ⟨i⟩ := RelEffCartierDiv.nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn
      c ε U E hEU Φ DY hDYU
    exact ⟨i ≪≫ eL.some.symm⟩

  have hpt : ∀ (k : Type u) [Field k] (s' : Spec (CommRingCat.of k) ⟶ T'),
      (∀ 𝒲 : (pullback (pullback.snd c (ψ ≫ t)) s').TwoAffineOpenCover,
        Subsingleton (𝒲.sectionsOf (fibreAt c (ψ ≫ t) s') (fibreModule c (ψ ≫ t) s'
          (Mγ R c ε E Dγ (ψ ≫ t) (L.pullbackAlong Ψ)))).H1) ∧
      FinerAt c U (ψ ≫ t) (Mγ R c ε E Dγ (ψ ≫ t) (L.pullbackAlong Ψ)) s' := by
    intro k _ s'

    have hrange : Set.range ⇑((s' ≫ φ') ≫ X.ι) ⊆ (X : Set WY) := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact ((s' ≫ φ') z).2
    obtain ⟨hH1, hfin⟩ := (hX k ((s' ≫ φ') ≫ X.ι)).1 hrange

    let ι : SchemeHomOver (WY.ι ≫ y) y := ⟨WY.ι, rfl⟩
    have hs : ((s' ≫ φ') ≫ X.ι) ≫ ι.1 = s' ≫ Φ.1 := by simp only [Category.assoc]; rfl
    have hH1Y := (forall_subsingleton_H1_congr_hom R c y _ hs).1
      (forall_subsingleton_H1_of_pullbackAlong R c ε U E hEU Dγ hDγ y (WY.ι ≫ y) ι (LY R c ε U E hEU y DY hDYU) _ hH1)
    have hfinY := (finerAt_congr_hom c U y _ hs).1
      ((finerAt_Mγ_pullbackAlong_iff R c ε U E hEU Dγ hDγ y (WY.ι ≫ y) ι (LY R c ε U E hEU y DY hDYU) _).1 hfin)

    refine ⟨fun 𝒲 => forall_subsingleton_H1_of_iso R c (ψ ≫ t) eM s'
        (forall_subsingleton_H1_pullbackAlong R c ε U E hEU Dγ hDγ y (ψ ≫ t) Φ (LY R c ε U E hEU y DY hDYU) s' hH1Y) 𝒲, ?_⟩
    exact (finerAt_congr_iso c U (ψ ≫ t) eM s').1
      ((finerAt_Mγ_pullbackAlong_iff R c ε U E hEU Dγ hDγ y (ψ ≫ t) Φ (LY R c ε U E hEU y DY hDYU) s').2 hfinY)

  obtain ⟨hrangeW, huniq⟩ := relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset R c ε U g e ρ hr
    E hEU Dγ hDγ hsect hZfibγ hH0one t L hL W (fun k _ _ s hH1 hfin => (hWiff k s).2 ⟨hH1, hfin⟩) D D₀ hD hD₀U hDL (ψ ≫ t) Ψ
    (DY.pullbackAlong (φ' ≫ jX WY X) h1) (𝒟.pullbackAlong (φ' ≫ jX WY X) h1) hD' (h𝒟U.pullbackAlong _ h1) hD'L
    (fun k _ s' => (hpt k s').1) (fun k _ _ x => (hpt k x).2)

  have hrangeW' : Set.range ⇑ψ ⊆ Set.range ⇑W.ι := by rw [Scheme.Opens.range_ι]; exact hrangeW
  refine ⟨IsOpenImmersion.lift W.ι ψ hrangeW', IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have hχt : IsOpenImmersion.lift W.ι ψ hrangeW' ≫ W.ι ≫ t = ψ ≫ t := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]

  have hDD := huniq (IsOpenImmersion.lift W.ι ψ hrangeW') (IsOpenImmersion.lift_fac _ _ _)
  have hI : (𝒟.pullbackAlong (φ' ≫ jX WY X) h1).I * (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).I =
      (D₀.pullbackAlong (IsOpenImmersion.lift W.ι ψ hrangeW') hχt).I *
        (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).I := by
    rw [← hD', hDD, pullbackAlong_I_eq_mul D D₀ _ hD _ hχt, RelEffCartierDiv.pullbackAlong_comp,
      pullbackAlong_congr_hom Dγ hχt _ (Category.comp_id _)]
  have hI' : (𝒟.pullbackAlong (φ' ≫ jX WY X) h1).I = (D₀.pullbackAlong (IsOpenImmersion.lift W.ι ψ hrangeW') hχt).I := by
    rw [mul_comm, mul_comm (D₀.pullbackAlong _ hχt).I] at hI
    exact (isInvertible_Dγ R c U Dγ hDγ (ψ ≫ t)).mul_left_cancel hI

  have e1 : φ' ≫ jX WY X = hulift R c U g y 𝒟 huniv (𝒟.pullbackAlong (φ' ≫ jX WY X) h1) (h𝒟U.pullbackAlong _ h1) :=
    eq_hulift R c U g y 𝒟 huniv _ (h𝒟U.pullbackAlong _ h1) h1 (pullsBackOver_pullbackAlong 𝒟 (φ' ≫ jX WY X) h1)
  have e2 : IsOpenImmersion.lift W.ι ψ hrangeW' ≫ hulift R c U g y 𝒟 huniv D₀ hD₀U =
      hulift R c U g y 𝒟 huniv (𝒟.pullbackAlong (φ' ≫ jX WY X) h1) (h𝒟U.pullbackAlong _ h1) := by
    refine eq_hulift R c U g y 𝒟 huniv _ (h𝒟U.pullbackAlong _ h1) (by rw [Category.assoc, hulift_comp R c U g y 𝒟 huniv D₀ hD₀U, hχt]) ?_
    change (𝒟.pullbackAlong (IsOpenImmersion.lift W.ι ψ hrangeW' ≫ hulift R c U g y 𝒟 huniv D₀ hD₀U) _).I =
      (𝒟.pullbackAlong (φ' ≫ jX WY X) h1).I
    rw [hI', ← RelEffCartierDiv.pullbackAlong_comp 𝒟 (hulift R c U g y 𝒟 huniv D₀ hD₀U) (hulift_comp R c U g y 𝒟 huniv D₀ hD₀U) _ hχt,
      pullbackAlong_hulift R c U g y 𝒟 huniv D₀ hD₀U]
  haveI : Mono (jX WY X) := inferInstance
  rw [← cancel_mono (jX WY X), Category.assoc, φ_jX, e2, ← e1]

end Chart
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard.FinTransport"
end AlgebraicGeometry.RelPicard.ChartE
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard.FinTransport P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard.ChartE"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard.FinTransport"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard.FinTransport"

open CategoryTheory CategoryTheory.Limits Opposite _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry _root_.AlgebraicGeometry.RelPicard _root_.P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.RelPicard.ChartE in

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεU : Set.range ε.1 ⊆ (U : Set C))

    (g e ρ : ℕ) (hr : g + e = ρ)

    (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)

    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (𝟙_ (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).Modules)).H1 = g)

    (Y : Scheme.{u}) (y : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType y] [CompactSpace Y]
    (Duniv : RelEffCartierDiv c g y) (hDunivU : Duniv.SupportedIn U)
    (huniv : ∀ ⦃T : Scheme.{u}⦄ (g' : T ⟶ Spec (CommRingCat.of R)) (D : RelEffCartierDiv c g g'), D.SupportedIn U →
        ∃! φ : {φ : T ⟶ Y // φ ≫ y = g'}, PullsBackOver Duniv φ.1 φ.2 D)
    (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hDγ : Dγ.SupportedIn U)
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (E.lineBundle ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (E.lineBundle ⊗ Dγ.idealModule))).H1 = 1)

    (hsect : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType u] (M : (pullback c u).Modules),
      Scheme.Modules.IsInvertible M →
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ V) (𝒲 : (pullback (pullback.snd c u) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H0 = 1) →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ V)
        (σ : 𝟙_ (pullback c (x ≫ u)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ u), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) →
      ∃ (D₀ : RelEffCartierDiv c g u) (N : V.Modules), Scheme.Modules.IsInvertible N ∧
        Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N) ∧
        ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' u) (N' : V.Modules), Scheme.Modules.IsInvertible N' → D'.SupportedIn U →
          Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N') → D'.I = D₀.I)

    (hZfibγ : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →

        ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ t))) ⊆ ((pullback.fst c (x ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ t))) →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)

    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)

    (havoid : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →

      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))),
        σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ t))) ⊆ ((pullback.fst c (x ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ t)))) →
      ∀ (D₀ : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N →
        Nonempty (D₀.lineBundle ≅
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ⊗
            (Scheme.Modules.pullback (pullback.snd c t)).obj N) →
        D₀.SupportedIn U)

    (hcut : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (D : RelEffCartierDiv c ρ t) (D₀ : RelEffCartierDiv c g t), D₀.SupportedIn U →
      D.I = D₀.I * (Dγ.pullbackAlong t (Category.comp_id t)).I →
      ∃ W : T.Opens, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ (W : Set T) ↔
          IsAlgEquivZero (fibreAt c t s)
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj (Scheme.Modules.rigidify (RelPicard.rigSection c t ε) (pullback.snd c t)
              (D.lineBundle ⊗ (E.pullbackAlong t (Category.comp_id t)).idealModule)))) :
    ∃ (X : Scheme.{u}) (f : uliftYoneda.{u + 1}.obj X ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv f).1 ∧ CompactSpace X ∧
      (∃ j : X ⟶ Y, IsOpenImmersion j ∧ j ≫ y = (uliftYonedaEquiv f).1) ∧
      ∀ ⦃T : Scheme.{u}⦄ (x : uliftYoneda.{u + 1}.obj T ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
        LocallyOfFiniteType (uliftYonedaEquiv x).1 →
        ∃ (U' : T.Opens) (φ : (↑U' : Scheme.{u}) ⟶ X),
          (∀ (L : RigidifiedLineBundle c ε (uliftYonedaEquiv x).1), Quotient.mk _ L = (uliftYonedaEquiv x).2.1 →
            ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
              Set.range ⇑s ⊆ (U' : Set T) ↔
                (∀ (𝒲 : (pullback (pullback.snd c (uliftYonedaEquiv x).1) s).TwoAffineOpenCover),
                  Subsingleton (𝒲.sectionsOf (fibreAt c (uliftYonedaEquiv x).1 s) (fibreModule c (uliftYonedaEquiv x).1 s
                    (L.L ⊗ ((E.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).lineBundle ⊗
                      (Dγ.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)))).H1) ∧

                (∀ σ : 𝟙_ (pullback c (s ≫ (uliftYonedaEquiv x).1)).Modules ⟶
                    (Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj
                      (L.L ⊗ ((E.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).lineBundle ⊗
                        (Dγ.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)),
                  σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (s ≫ (uliftYonedaEquiv x).1))) ⊆
                    ((pullback.fst c (s ≫ (uliftYonedaEquiv x).1)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫ (uliftYonedaEquiv x).1))))) ∧
          uliftYoneda.{u + 1}.map φ ≫ f = uliftYoneda.{u + 1}.map U'.ι ≫ x ∧
          ∀ ⦃T' : Scheme.{u}⦄ (ψ : T' ⟶ T) (φ' : T' ⟶ X),
            LocallyOfFiniteType (ψ ≫ (uliftYonedaEquiv x).1) →
            uliftYoneda.{u + 1}.map φ' ≫ f = uliftYoneda.{u + 1}.map ψ ≫ x →
            ∃ χ : T' ⟶ ↑U', χ ≫ U'.ι = ψ ∧ χ ≫ φ = φ' := by
  subst hr

  obtain ⟨DY, hDY, hDYU⟩ := RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn U Duniv
    (Dγ.pullbackAlong y (Category.comp_id y)) hDunivU (hDγ.pullbackAlong y (Category.comp_id y))

  obtain ⟨WY, hWY⟩ := hcut y DY Duniv hDunivU hDY

  obtain ⟨X, hX⟩ := exists_finerOpen R c ε U E hEU 𝒱 g e rfl Dγ hDγ hH0one (WY.ι ≫ y)
    ((LY R c ε U E hEU y DY hDYU).pullbackAlong (⟨WY.ι, rfl⟩ : SchemeHomOver (WY.ι ≫ y) y))
    (fibrewiseAlgEquivZero_LY_WY R c ε U E hEU 𝒱 g e rfl Dγ hDγ hsect hZfibγ hH0one y Duniv hDunivU huniv DY hDY hDYU WY hWY)
  refine ⟨(X : Scheme.{u}), chartMap R c ε U E hEU 𝒱 g e rfl Dγ hDγ hsect hZfibγ hH0one y Duniv hDunivU huniv DY hDY hDYU WY hWY X hX, ?_, ?_, ?_, ?_⟩
  ·
    rw [uliftYonedaEquiv_chartMap]
    change LocallyOfFiniteType ((X.ι ≫ WY.ι) ≫ y)
    infer_instance
  ·
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian y
    haveI : IsNoetherian Y := {}
    haveI : IsLocallyNoetherian (WY : Scheme.{u}) := inferInstance
    haveI : CompactSpace (WY : Scheme.{u}) := by
      change CompactSpace (WY : Set Y)
      exact isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
    haveI : IsNoetherian (WY : Scheme.{u}) := {}
    change CompactSpace (X : Set (WY : Scheme.{u}))
    exact isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  ·
    refine ⟨X.ι ≫ WY.ι, inferInstance, ?_⟩
    rw [uliftYonedaEquiv_chartMap]; rfl
  intro T x hx

  generalize hxa : uliftYonedaEquiv x = a at hx ⊢
  obtain rfl : x = uliftYonedaEquiv.symm a := by rw [← hxa, Equiv.symm_apply_apply]
  clear hxa
  change (relSubPicPresheaf c ε (algEquivZeroCut c ε)).OverTotal T at a
  obtain ⟨t, ⟨ξ, hξ⟩⟩ := a
  obtain ⟨L, rfl⟩ := Quotient.exists_rep ξ
  change FibrewiseAlgEquivZero L at hξ
  haveI : LocallyOfFiniteType t := hx
  change ∃ (W : T.Opens) (φ : (W : Scheme.{u}) ⟶ (X : Scheme.{u})), _ ∧
    uliftYoneda.{u + 1}.map φ ≫ _ = uliftYoneda.{u + 1}.map W.ι ≫ uliftYonedaEquiv.symm (pointElem R c ε t L hξ) ∧ _

  obtain ⟨W, hWiff⟩ := exists_finerOpen R c ε U E hEU 𝒱 g e rfl Dγ hDγ hH0one t L hξ
  have hWfin : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u})),
      FinerAt c U (W.ι ≫ t) (Mγ R c ε E Dγ (W.ι ≫ t) (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t))) x := by
    intro k _ _ x
    have hrange : Set.range ⇑(x ≫ W.ι) ⊆ (W : Set T) := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact (x z).2
    exact (finerAt_Mγ_pullbackAlong_iff R c ε U E hEU Dγ hDγ t (W.ι ≫ t) ⟨W.ι, rfl⟩ L x).2 ((hWiff k (x ≫ W.ι)).1 hrange).2
  obtain ⟨D, D₀, hD, hDL, hD₀U⟩ :=
    exists_relEffCartierDiv_supportedIn_rigidify_iso_of_subsingleton_H1_of_support_subset R c ε U g e (g + e) rfl
      E hEU Dγ hDγ hsect hZfibγ hH0one havoid t L hξ W (fun k _ s hs => ((hWiff k s).1 hs).1) hWfin
  refine ⟨W, φ R c ε U E hEU 𝒱 g e rfl Dγ hDγ hsect hZfibγ hH0one y Duniv hDunivU huniv DY hDY hDYU WY hWY X hX t L hξ W hWiff D D₀ hD hDL hD₀U, ?_, ?_, ?_⟩
  · intro L' hL' k _ s
    exact clause_i R c ε U E hEU 𝒱 g e rfl Dγ hDγ hsect hZfibγ hH0one y Duniv hDunivU huniv DY hDY hDYU WY hWY X hX t L hξ W hWiff D D₀ hD hDL hD₀U L' (Quotient.exact hL') k s
  · exact clause_ii R c ε U E hEU 𝒱 g e rfl Dγ hDγ hsect hZfibγ hH0one y Duniv hDunivU huniv DY hDY hDYU WY hWY X hX t L hξ W hWiff D D₀ hD hDL hD₀U
  · intro T' ψ φ' hlft hφ'
    haveI := hlft
    exact clause_iii R c ε U E hEU 𝒱 g e rfl Dγ hDγ hsect hZfibγ hH0one y Duniv hDunivU huniv DY hDY hDYU WY hWY X hX t L hξ W hWiff D D₀ hD hDL hD₀U ψ φ' hφ'

end S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_polarisation_of_fibrewise_zeroScheme (solution)
