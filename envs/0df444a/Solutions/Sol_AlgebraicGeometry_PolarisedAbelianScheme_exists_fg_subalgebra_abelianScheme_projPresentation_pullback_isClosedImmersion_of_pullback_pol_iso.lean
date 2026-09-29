-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3dfe29fe-fa82-5d4a-b26b-9e874576b03c

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso_of_pullback_pol_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_unit_eq_of_isDirectLimit
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_iSup_preimage_eq_top_of_isDirectLimit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

noncomputable section

universe u

section E20KIT

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.AlgebraicGeometry NeronModelInfra GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw CerednikDrinfeld.QM AlgebraicGeometry.PolarisedAbelianScheme"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Spec.map_comp Scheme.Modules.Hom.app_smul Scheme.IdealSheafData.support_comap Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom IsFinite QuasiCompact Spec Spec.map Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Proj Flat IsClosedImmersion Scheme.mem_zeroLocus_iff Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules.pullbackId Proj.basicOpen Scheme.Modules QuasiSeparated Scheme.Hom.preimage_iSup GeometricallyConnected LocallyOfFinitePresentation Scheme.basicOpen_one Proj.iSup_basicOpen_eq_top Scheme.Hom.comp_preimage Scheme.Modules.conjugateEquiv_pullbackComp_inv Scheme.IdealSheafData.mem_support_iff_of_mem geometrically Scheme.IdealSheafData Scheme.Modules.pullbackComp PolarisedAbelianScheme Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.ProjPresentation ProjSpace.π ProjSpace.irrelevant_le_span_X ProjSpace.map Scheme.Modules.pullbackLocalSection Scheme.Modules.pullbackLocalSection_app Scheme.Modules.IsFrameOn Scheme.Modules.toUnitSection Scheme.Modules.ofUnitSection Scheme.Modules.ofUnitSection_toUnitSection Scheme.Modules.ofUnitSection_injective Scheme.Modules.ofUnitSection_map Scheme.Modules.ofUnitSection_smul Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.pullbackSection_def PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso_of_pullback_pol_iso Scheme.Modules.IsInvertible.exists_forall_app_unit_eq_of_isDirectLimit Scheme.exists_iSup_preimage_eq_top_of_isDirectLimit Scheme.Modules.exists_projPresentation_of_iSup_eq_top Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback Scheme.Modules.ProjPresentation.exists_of_iso Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq ProjSpace.isPullback_map Scheme.Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal Scheme.Modules.IsInvertible.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext Modules.Hom.app_smul IdealSheafData.support_comap ringCatSheaf Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app mem_zeroLocus_iff Hom.comp_app basicOpen Modules.pullbackCongr Modules.pullbackPushforwardAdjunction Modules.pullbackId isBasis_affineOpens Modules Hom.preimage_iSup Opens basicOpen_one Hom.comp_preimage Modules.conjugateEquiv_pullbackComp_inv IdealSheafData.mem_support_iff_of_mem PresheafOfModules IdealSheafData Modules.pullbackComp Modules.IsInvertible Modules.pullbackUnitIso Modules.ProjPresentation Modules.pullbackLocalSection Modules.pullbackLocalSection_app Modules.IsFrameOn Modules.toUnitSection Modules.ofUnitSection Modules.ofUnitSection_toUnitSection Modules.ofUnitSection_injective Modules.ofUnitSection_map Modules.ofUnitSection_smul Modules.zeroSchemeIdeal Modules.pullbackSection Modules.pullbackSection_def Modules.IsInvertible.exists_forall_app_unit_eq_of_isDirectLimit exists_iSup_preimage_eq_top_of_isDirectLimit Modules.exists_projPresentation_of_iSup_eq_top Modules.ProjPresentation.exists_baseChange_of_isPullback Modules.ProjPresentation.exists_of_iso Modules.ProjPresentation.toProj_eq_of_forall_sections_eq Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal Modules.IsInvertible.comap_zeroSchemeIdeal Modules.IsInvertible.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection Modules.zeroSchemeIdeal_comp_eq_of_isIso"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.app_smul pushforwardComp pullback presheaf Hom.comp_app Hom pushforward_map_app Hom.id_app Hom.app pullbackCongr pullbackPushforwardAdjunction pullbackId conjugateEquiv_pullbackComp_inv pullbackComp IsInvertible pullbackUnitIso ProjPresentation pullbackLocalSection pullbackLocalSection_app IsFrameOn toUnitSection ofUnitSection ofUnitSection_toUnitSection ofUnitSection_injective ofUnitSection_map ofUnitSection_smul zeroSchemeIdeal pullbackSection pullbackSection_def IsInvertible.exists_forall_app_unit_eq_of_isDirectLimit exists_projPresentation_of_iSup_eq_top ProjPresentation.exists_baseChange_of_isPullback ProjPresentation.exists_of_iso ProjPresentation.toProj_eq_of_forall_sections_eq IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal IsInvertible.comap_zeroSchemeIdeal IsInvertible.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection zeroSchemeIdeal_comp_eq_of_isIso"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem pullbackComp_inv_app_app_pullbackLocalSection {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U) (pullbackLocalSection (f ≫ g) m) =
      pullbackLocalSection f (pullbackLocalSection g m) := by
  have h1 := CategoryTheory.unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h1
  have h2 := congrArg (fun k => Scheme.Modules.Hom.app k U m) h1
  dsimp only at h2
  erw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app] at h2
  erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h2

  exact h2.symm

theorem pullbackComp_hom_app_app_pullbackLocalSection {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app (f ⁻¹ᵁ (g ⁻¹ᵁ U))
        (pullbackLocalSection f (pullbackLocalSection g m)) =
      pullbackLocalSection (f ≫ g) m := by
  rw [← pullbackComp_inv_app_app_pullbackLocalSection]
  change (((Scheme.Modules.pullbackComp f g).inv.app M) ≫ ((Scheme.Modules.pullbackComp f g).hom.app M)).app
    ((f ≫ g) ⁻¹ᵁ U) (pullbackLocalSection (f ≫ g) m) = _
  rw [Iso.inv_hom_id_app, Scheme.Modules.Hom.id_app]
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace NoethBC20

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem mul_coe_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f)
    (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (G.mul t₁ P₁ Q₁).1 = (G.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

theorem one_coe_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) : (G.one t₁).1 = (G.one t₂).1 := by
  subst h; rfl

theorem inv_coe_congr (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (P₁ : SchemeHomOver t₁ f) (P₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) :
    (G.inv t₁ P₁).1 = (G.inv t₂ P₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  rfl

theorem toBase_injective {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    Function.Injective
      (baseChangePointToBase ι : SchemeHomOver t' (baseChangeStr ι f) → SchemeHomOver (t' ≫ ι) f) :=
  (baseChangePointEquiv ι t').injective

section Endo

variable (φ : A ⟶ A) (hφ : φ ≫ f = f)

def bcEndo : baseChangeScheme ι f ⟶ baseChangeScheme ι f :=
  pullback.lift (pullback.fst f ι ≫ φ) (pullback.snd f ι) (by rw [Category.assoc, hφ, pullback.condition])

@[reassoc (attr := simp)]
theorem bcEndo_fst : bcEndo ι φ hφ ≫ pullback.fst f ι = pullback.fst f ι ≫ φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcEndo_snd : bcEndo ι φ hφ ≫ pullback.snd f ι = pullback.snd f ι :=
  pullback.lift_snd _ _ _

theorem bcEndo_over : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f :=
  pullback.lift_snd _ _ _

theorem bcEndo_congr {φ ψ : A ⟶ A} (h : φ = ψ) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f) :
    bcEndo ι φ hφ = bcEndo ι ψ hψ := by
  subst h; rfl

theorem bcEndo_eq_id {φ : A ⟶ A} (h : φ = 𝟙 A) (hφ : φ ≫ f = f) : bcEndo ι φ hφ = 𝟙 _ := by
  subst h
  apply pullback.hom_ext
  · rw [bcEndo_fst, Category.id_comp, Category.comp_id]
  · rw [bcEndo_snd, Category.id_comp]

theorem bcEndo_eq_comp {χ ψ φ : A ⟶ A} (h : χ = ψ ≫ φ) (hχ : χ ≫ f = f) (hψ : ψ ≫ f = f) (hφ : φ ≫ f = f) :
    bcEndo ι χ hχ = bcEndo ι ψ hψ ≫ bcEndo ι φ hφ := by
  subst h
  apply pullback.hom_ext
  · simp only [bcEndo_fst, Category.assoc, bcEndo_fst_assoc]
  · simp only [bcEndo_snd, Category.assoc]

theorem toBase_pushPt {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (h' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    (P : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι (pushPt (bcEndo ι φ hφ) h' P) = pushPt φ hφ (baseChangePointToBase ι P) := by
  apply Subtype.ext
  simp only [baseChangePointToBase_coe, mapPt_coe, Category.assoc, bcEndo_fst]

theorem pushPt_bcEndo_mul (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (G.mul t P Q) = G.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    (h' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (baseChangeStr ι f)) :
    pushPt (bcEndo ι φ hφ) h' ((G.baseChange ι).mul t' P Q) =
      (G.baseChange ι).mul t' (pushPt (bcEndo ι φ hφ) h' P) (pushPt (bcEndo ι φ hφ) h' Q) := by
  apply toBase_injective ι t'
  rw [toBase_pushPt, baseChangePointToBase_mul, baseChangePointToBase_mul, H, toBase_pushPt, toBase_pushPt]

theorem pushPt_bcEndo_add (G : RelativeGroupLaw R f) {χ ψ : A ⟶ A} (hχ : χ ≫ f = f) (hψ : ψ ≫ f = f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt χ hχ P = G.mul t (pushPt φ hφ P) (pushPt ψ hψ P))
    (hχ' : bcEndo ι χ hχ ≫ baseChangeStr ι f = baseChangeStr ι f)
    (hφ' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    (hψ' : bcEndo ι ψ hψ ≫ baseChangeStr ι f = baseChangeStr ι f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    pushPt (bcEndo ι χ hχ) hχ' P =
      (G.baseChange ι).mul t' (pushPt (bcEndo ι φ hφ) hφ' P) (pushPt (bcEndo ι ψ hψ) hψ' P) := by
  apply toBase_injective ι t'
  rw [toBase_pushPt, baseChangePointToBase_mul, H, toBase_pushPt, toBase_pushPt]

end Endo

section Lev

variable (f) {C : Scheme.{u}} (lev : C ⟶ A)

abbrev bcLevScheme : Scheme.{u} :=
  pullback (lev ≫ f) ι

def bcLev : bcLevScheme ι f lev ⟶ baseChangeScheme ι f :=
  pullback.lift (pullback.fst (lev ≫ f) ι ≫ lev) (pullback.snd (lev ≫ f) ι)
    (by rw [Category.assoc]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem bcLev_fst : bcLev ι f lev ≫ pullback.fst f ι = pullback.fst (lev ≫ f) ι ≫ lev :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcLev_snd : bcLev ι f lev ≫ pullback.snd f ι = pullback.snd (lev ≫ f) ι :=
  pullback.lift_snd _ _ _

theorem bcLev_comp_baseChangeStr : bcLev ι f lev ≫ baseChangeStr ι f = pullback.snd (lev ≫ f) ι :=
  pullback.lift_snd _ _ _

theorem isPullback_fst_bcLev :
    IsPullback (pullback.fst (lev ≫ f) ι) (bcLev ι f lev) lev (pullback.fst f ι) := by
  refine IsPullback.of_bot ?_ (bcLev_fst ι f lev).symm (IsPullback.of_hasPullback f ι)
  rw [bcLev_snd]
  exact IsPullback.of_hasPullback (lev ≫ f) ι

theorem isClosedImmersion_bcLev [IsClosedImmersion lev] : IsClosedImmersion (bcLev ι f lev) :=
  MorphismProperty.of_isPullback (isPullback_fst_bcLev ι f lev) ‹_›

theorem isFinite_bcLev_comp [IsFinite (lev ≫ f)] : IsFinite (bcLev ι f lev ≫ baseChangeStr ι f) := by
  rw [bcLev_comp_baseChangeStr]; infer_instance

theorem flat_bcLev_comp [Flat (lev ≫ f)] : Flat (bcLev ι f lev ≫ baseChangeStr ι f) := by
  rw [bcLev_comp_baseChangeStr]; infer_instance

theorem locallyOfFinitePresentation_bcLev_comp [LocallyOfFinitePresentation (lev ≫ f)] :
    LocallyOfFinitePresentation (bcLev ι f lev ≫ baseChangeStr ι f) := by
  rw [bcLev_comp_baseChangeStr]; infer_instance

theorem factorsThrough_bcLev_iff {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P ↔ FactorsThrough lev (baseChangePointToBase ι P) := by
  constructor
  · rintro ⟨P₀, hP₀⟩
    refine ⟨P₀ ≫ pullback.fst (lev ≫ f) ι, ?_⟩
    rw [baseChangePointToBase_coe, ← hP₀, Category.assoc, Category.assoc, bcLev_fst]
  · rintro ⟨Q₀, hQ₀⟩
    rw [baseChangePointToBase_coe] at hQ₀
    refine ⟨pullback.lift Q₀ (P.1 ≫ pullback.snd f ι) ?_, ?_⟩
    · rw [← Category.assoc, hQ₀, Category.assoc, Category.assoc, pullback.condition]
    · apply pullback.hom_ext
      · rw [Category.assoc, bcLev_fst, ← Category.assoc, pullback.lift_fst, hQ₀]
      · rw [Category.assoc, bcLev_snd, pullback.lift_snd]

theorem toBase_nsmulPt (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (n : ℕ) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι (nsmulPt (G.baseChange ι) t' n P) =
      nsmulPt G (t' ≫ ι) n (baseChangePointToBase ι P) := by
  induction n with
  | zero => exact baseChangePointToBase_one ι G t'
  | succ n ih => simp only [nsmulPt, baseChangePointToBase_mul, ih]

theorem lev_sub_bc (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (G.mul t P Q) ∧ FactorsThrough lev (G.inv t P))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → FactorsThrough (bcLev ι f lev) Q →
      FactorsThrough (bcLev ι f lev) ((G.baseChange ι).mul t' P Q) ∧
        FactorsThrough (bcLev ι f lev) ((G.baseChange ι).inv t' P) := by
  intro hP hQ
  rw [factorsThrough_bcLev_iff] at hP hQ
  rw [factorsThrough_bcLev_iff, factorsThrough_bcLev_iff, baseChangePointToBase_mul, baseChangePointToBase_inv]
  exact H _ _ _ hP hQ

theorem lev_one_bc (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough lev (G.one t))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    FactorsThrough (bcLev ι f lev) ((G.baseChange ι).one t') := by
  rw [factorsThrough_bcLev_iff, baseChangePointToBase_one]
  exact H _

theorem lev_torsion_bc (G : RelativeGroupLaw R f) (N : ℕ)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      FactorsThrough lev P → nsmulPt G t N P = G.one t)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → nsmulPt (G.baseChange ι) t' N P = (G.baseChange ι).one t' := by
  intro hP
  rw [factorsThrough_bcLev_iff] at hP
  apply toBase_injective ι t'
  rw [toBase_nsmulPt, baseChangePointToBase_one]
  exact H _ _ hP

theorem lev_stable_bc (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev (pushPt φ hφ P))
    (h' : bcEndo ι φ hφ ≫ baseChangeStr ι f = baseChangeStr ι f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' (baseChangeStr ι f)) :
    FactorsThrough (bcLev ι f lev) P → FactorsThrough (bcLev ι f lev) (pushPt (bcEndo ι φ hφ) h' P) := by
  intro hP
  rw [factorsThrough_bcLev_iff] at hP
  rw [factorsThrough_bcLev_iff, toBase_pushPt]
  exact H _ _ hP

end Lev

theorem geometricallyConnected_baseChangeStr [GeometricallyConnected f] :
    GeometricallyConnected (baseChangeStr ι f) :=
  inferInstance

theorem abelianSchemePropertyBundle_bc (hb : AbelianSchemePropertyBundle R f) [GeometricallyConnected f]
    (G' : RelativeGroupLaw R' (baseChangeStr ι f)) :
    AbelianSchemePropertyBundle R' (baseChangeStr ι f) where
  smooth := have := hb.smooth; inferInstance
  proper := have := hb.proper; inferInstance
  connectedFibres s := (baseChangeStr ι f).isConnected_preimage_singleton s
  hasGroupLaw := ⟨G'⟩

section Comparison

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of S))
variable (j : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) (j' : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R'))
variable (hj : j' ≫ ι = j) (g : X ⟶ A) (hg : IsPullback g p f j)

def bcComparison : X ⟶ baseChangeScheme ι f :=
  pullback.lift g (p ≫ j') (by rw [Category.assoc, hj]; exact hg.w)

@[reassoc (attr := simp)]
theorem bcComparison_fst : bcComparison ι p j j' hj g hg ≫ pullback.fst f ι = g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcComparison_snd : bcComparison ι p j j' hj g hg ≫ pullback.snd f ι = p ≫ j' :=
  pullback.lift_snd _ _ _

theorem isPullback_bcComparison :
    IsPullback (bcComparison ι p j j' hj g hg) p (baseChangeStr ι f) j' := by
  refine IsPullback.of_right ?_ (bcComparison_snd ι p j j' hj g hg) (IsPullback.of_hasPullback f ι)
  rw [bcComparison_fst, hj]
  exact hg

theorem comp_bcComparison_eq_bcComparison_comp_bcEndo (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (actX : X ⟶ X) (hactX : actX ≫ p = p) (H : actX ≫ g = g ≫ φ) :
    actX ≫ bcComparison ι p j j' hj g hg = bcComparison ι p j j' hj g hg ≫ bcEndo ι φ hφ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcComparison_fst, bcEndo_fst, bcComparison_fst_assoc, H]
  · simp only [Category.assoc, bcComparison_snd, bcEndo_snd]
    rw [← Category.assoc, hactX]

theorem mul_coe_comp_bcComparison (GX : RelativeGroupLaw S p) (G : RelativeGroupLaw R f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t p),
      (GX.mul t P Q).1 ≫ g =
        (G.mul (t ≫ j) ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t p) :
    (GX.mul t P Q).1 ≫ bcComparison ι p j j' hj g hg =
      ((G.baseChange ι).mul (t ≫ j')
        ⟨P.1 ≫ bcComparison ι p j j' hj g hg, by
          rw [Category.assoc, (isPullback_bcComparison ι p j j' hj g hg).w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ bcComparison ι p j j' hj g hg, by
          rw [Category.assoc, (isPullback_bcComparison ι p j j' hj g hg).w, ← Category.assoc, Q.2]⟩).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcComparison_fst, H, baseChange_mul, baseChangePointOfBase_coe, pullback.lift_fst]
    apply mul_coe_congr G
    · rw [Category.assoc, hj]
    · simp only [baseChangePointToBase_coe, Category.assoc, bcComparison_fst]
    · simp only [baseChangePointToBase_coe, Category.assoc, bcComparison_fst]
  · have e1 : ∀ x : SchemeHomOver (t ≫ j') (baseChangeStr ι f), x.1 ≫ pullback.snd f ι = t ≫ j' :=
      fun x => x.2
    rw [e1]
    simp only [Category.assoc, bcComparison_snd]
    rw [← Category.assoc, (GX.mul t P Q).2]

section Sub

variable {C : Scheme.{u}} (lev : C ⟶ A) {XC : Scheme.{u}} (pC : XC ⟶ X) (gC : XC ⟶ C)
variable (hgC : IsPullback gC pC lev g)

def bcComparisonSub : XC ⟶ bcLevScheme ι f lev :=
  pullback.lift gC (pC ≫ p ≫ j') (by
    rw [← Category.assoc gC, hgC.w, Category.assoc, hg.w, Category.assoc, Category.assoc, hj])

@[reassoc (attr := simp)]
theorem bcComparisonSub_fst : bcComparisonSub ι p j j' hj g hg lev pC gC hgC ≫ pullback.fst (lev ≫ f) ι = gC :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcComparisonSub_snd :
    bcComparisonSub ι p j j' hj g hg lev pC gC hgC ≫ pullback.snd (lev ≫ f) ι = pC ≫ p ≫ j' :=
  pullback.lift_snd _ _ _

theorem bcComparisonSub_bcLev :
    bcComparisonSub ι p j j' hj g hg lev pC gC hgC ≫ bcLev ι f lev = pC ≫ bcComparison ι p j j' hj g hg := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcLev_fst, bcComparisonSub_fst_assoc, bcComparison_fst]
    exact hgC.w
  · simp only [Category.assoc, bcLev_snd, bcComparisonSub_snd, bcComparison_snd]

theorem isPullback_bcComparisonSub :
    IsPullback (bcComparisonSub ι p j j' hj g hg lev pC gC hgC) pC (bcLev ι f lev)
      (bcComparison ι p j j' hj g hg) := by
  refine IsPullback.of_right ?_ (bcComparisonSub_bcLev ι p j j' hj g hg lev pC gC hgC) (isPullback_fst_bcLev ι f lev)
  rw [bcComparisonSub_fst, bcComparison_fst]
  exact hgC

end Sub

end Comparison

end NoethBC20

namespace FGStages20

variable {A₀ : Type} [CommRing A₀] {A : Type} [CommRing A] [Algebra A₀ A] (B : Subalgebra A₀ A)

abbrev Idx : Type := {T : Subalgebra A₀ A // T.FG ∧ B ≤ T}

abbrev G (i : Idx B) : Type := ↥i.1

def φ (i j : Idx B) (h : i ≤ j) : G B i →+* G B j := (Subalgebra.inclusion (show i.1 ≤ j.1 from h)).toRingHom

def g (i : Idx B) : G B i →+* A := (i.1).val.toRingHom

@[scoped simp] theorem φ_apply (i j : Idx B) (h : i ≤ j) (x : G B i) : (φ B i j h x : A) = (x : A) := rfl
@[scoped simp] theorem g_apply (i : Idx B) (x : G B i) : g B i x = (x : A) := rfl

scoped instance : DirectedSystem (G B) (fun i j h => ⇑(φ B i j h)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

private def _root_.FGStages20.sup (i j : Idx B) : Idx B := ⟨i.1 ⊔ j.1, i.2.1.sup j.2.1, le_sup_of_le_left i.2.2⟩

p2m_export "FGStages20" "sup"
scoped instance : IsDirected (Idx B) (· ≤ ·) :=
  ⟨fun i j => ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩⟩

theorem nonempty (hB : B.FG) : Nonempty (Idx B) := ⟨⟨B, hB, le_rfl⟩⟩

theorem isDirectLimit (hB : B.FG) : IsDirectLimit (fun i j h => ⇑(φ B i j h)) (fun i => ⇑(g B i)) where
  surj m := by
    refine ⟨⟨B ⊔ Algebra.adjoin A₀ {m}, hB.sup ⟨{m}, by rw [Finset.coe_singleton]⟩, le_sup_left⟩, ⟨m, ?_⟩, rfl⟩
    exact Algebra.mem_sup_right (Algebra.self_mem_adjoin_singleton A₀ m)
  inj i j mi mj h := ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1), Subtype.ext h⟩
  compatibility _ _ _ _ := rfl

end FGStages20
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.FGStages20"

namespace SPKit20

open NoethBC20

section

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem isIso_bcEndo (φ : A ⟶ A) (hφ : φ ≫ f = f) [IsIso φ] : IsIso (bcEndo ι φ hφ) := by
  have hφ' : inv φ ≫ f = f := by rw [← cancel_epi φ, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp, hφ]
  refine ⟨⟨bcEndo ι (inv φ) hφ', ?_, ?_⟩⟩
  · rw [← bcEndo_eq_comp ι (IsIso.hom_inv_id φ).symm (Category.id_comp f) hφ hφ']
    exact bcEndo_eq_id ι rfl _
  · rw [← bcEndo_eq_comp ι (IsIso.inv_hom_id φ).symm (Category.id_comp f) hφ' hφ]
    exact bcEndo_eq_id ι rfl _

def bcOver (σ : SchemeHomOver f f) : SchemeHomOver (baseChangeStr ι f) (baseChangeStr ι f) :=
  ⟨bcEndo ι σ.1 σ.2, bcEndo_over ι σ.1 σ.2⟩

@[scoped simp] theorem bcOver_coe (σ : SchemeHomOver f f) : (bcOver ι σ).1 = bcEndo ι σ.1 σ.2 := rfl

theorem schemeHomOverComp_bcOver_mul (G : RelativeGroupLaw R f) (σ : SchemeHomOver f f)
    (H : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (G.mul t x y) σ =
        G.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t (baseChangeStr ι f)) :
    NeronModelInfra.schemeHomOverComp ((G.baseChange ι).mul t x y) (bcOver ι σ) =
      (G.baseChange ι).mul t (NeronModelInfra.schemeHomOverComp x (bcOver ι σ))
        (NeronModelInfra.schemeHomOverComp y (bcOver ι σ)) :=
  pushPt_bcEndo_mul ι σ.1 σ.2 G H (bcEndo_over ι σ.1 σ.2) t x y

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.FGStages20"

theorem nonempty_pullback_iso {X P P' : Scheme.{u}} (e : X ≅ P) (cX : P ⟶ P') (gA : X ⟶ P')
    (hgA : gA = e.hom ≫ cX) (M' : P'.Modules) (N : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback cX).obj M' ≅ (Scheme.Modules.pullback e.inv).obj N)) :
    Nonempty ((Scheme.Modules.pullback gA).obj M' ≅ N) := by
  obtain ⟨e₁⟩ := h
  exact ⟨(Scheme.Modules.pullbackCongr hgA).app M' ≪≫ ((Scheme.Modules.pullbackComp e.hom cX).app M').symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso e₁ ≪≫ (Scheme.Modules.pullbackComp e.hom e.inv).app N ≪≫
    (Scheme.Modules.pullbackCongr e.hom_inv_id).app N ≪≫ (Scheme.Modules.pullbackId X).app N⟩

end SPKit20
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.SPKit20"

namespace SPD20

p2m_open "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.NoethBC20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.SPKit20 AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.AlgebraicGeometry.Scheme.Modules"

theorem iSup_preimage_comp_eq_top {Z W V : Scheme.{u}} (a : Z ⟶ W) (b : W ⟶ V) {κ : Type*} (U : κ → V.Opens)
    (h : (⨆ k, b ⁻¹ᵁ U k) = ⊤) : (⨆ k, (a ≫ b) ⁻¹ᵁ U k) = ⊤ := by
  simp_rw [Scheme.Hom.comp_preimage]
  rw [← Scheme.Hom.preimage_iSup, h]
  rfl

section

variable {k : Type} [Field k] (R : Subalgebra ℤ k) (hR : R.FG)
variable {A₀ : Scheme.{0}} (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (M₀ : A₀.Modules)
variable {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (gA : X ⟶ A₀)
variable (hg : IsPullback gA p f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))

abbrev i₀ : FGStages20.Idx R := ⟨R, hR, le_rfl⟩

abbrev ιst (j : FGStages20.Idx R) (hij : i₀ R hR ≤ j) : Spec (CommRingCat.of ↥j.1) ⟶ Spec (CommRingCat.of ↥R) :=
  Spec.map (CommRingCat.ofHom (FGStages20.φ R (i₀ R hR) j hij))

theorem specLeg_ιst (j : FGStages20.Idx R) (hij : i₀ R hR ≤ j) :
    Spec.map (CommRingCat.ofHom (j.1).val.toRingHom) ≫ ιst R hR j hij = Spec.map (CommRingCat.ofHom R.val.toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem specTrans_ιst (j j' : FGStages20.Idx R) (hij : i₀ R hR ≤ j) (hjj' : j ≤ j') :
    Spec.map (CommRingCat.ofHom (FGStages20.φ R j j' hjj')) ≫ ιst R hR j hij = ιst R hR j' (hij.trans hjj') := by
  rw [ιst, ιst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem specLeg_specTrans (j j' : FGStages20.Idx R) (hjj' : j ≤ j') :
    Spec.map (CommRingCat.ofHom (j'.1).val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (FGStages20.φ R j j' hjj')) =
      Spec.map (CommRingCat.ofHom (j.1).val.toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

abbrev cst (j : FGStages20.Idx R) (hij : i₀ R hR ≤ j) : X ⟶ pullback f₀ (ιst R hR j hij) :=
  bcComparison (ιst R hR j hij) p _ _ (specLeg_ιst R hR j hij) gA hg

private def _root_.SPD20.trans (j j' : FGStages20.Idx R) (hij : i₀ R hR ≤ j) (hjj' : j ≤ j') :
    pullback f₀ (ιst R hR j' (hij.trans hjj')) ⟶ pullback f₀ (ιst R hR j hij) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (FGStages20.φ R j j' hjj')))
    (by rw [Category.assoc, specTrans_ιst]; exact pullback.condition)

p2m_export "SPD20" "trans"
@[reassoc (attr := simp)]
theorem trans_fst (j j' : FGStages20.Idx R) (hij : i₀ R hR ≤ j) (hjj' : j ≤ j') :
    trans R hR f₀ j j' hij hjj' ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem trans_snd (j j' : FGStages20.Idx R) (hij : i₀ R hR ≤ j) (hjj' : j ≤ j') :
    trans R hR f₀ j j' hij hjj' ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (FGStages20.φ R j j' hjj')) := pullback.lift_snd _ _ _

theorem cst_trans (j j' : FGStages20.Idx R) (hij : i₀ R hR ≤ j) (hjj' : j ≤ j') :
    cst R hR f₀ p gA hg j' (hij.trans hjj') ≫ trans R hR f₀ j j' hij hjj' = cst R hR f₀ p gA hg j hij := by
  apply pullback.hom_ext
  · rw [Category.assoc, trans_fst, bcComparison_fst, bcComparison_fst]
  · rw [Category.assoc, trans_snd, ← Category.assoc, bcComparison_snd, bcComparison_snd, Category.assoc,
      specLeg_specTrans]

theorem exists_stage_cover [QuasiCompact f₀] [QuasiSeparated f₀]
    (j : FGStages20.Idx R) (hij : i₀ R hR ≤ j) {κ : Type} (U : κ → (pullback f₀ (ιst R hR j hij)).Opens)
    (hcov : (⨆ l, (cst R hR f₀ p gA hg j hij) ⁻¹ᵁ U l) = ⊤) :
    ∃ (j' : FGStages20.Idx R) (hjj' : j ≤ j'), (⨆ l, (trans R hR f₀ j j' hij hjj') ⁻¹ᵁ U l) = ⊤ := by
  haveI : Nonempty (FGStages20.Idx R) := FGStages20.nonempty R hR
  have hc := isPullback_bcComparison (ιst R hR j hij) p _ _ (specLeg_ιst R hR j hij) gA hg
  have hcovZ := iSup_preimage_comp_eq_top hc.isoPullback.inv _ U hcov
  rw [hc.isoPullback_inv_fst] at hcovZ
  obtain ⟨j', hjj', hcov'⟩ :=
    AlgebraicGeometry.Scheme.exists_iSup_preimage_eq_top_of_isDirectLimit (FGStages20.φ R) (FGStages20.g R)
      (FGStages20.isDirectLimit R hR) j (pullback.snd f₀ (ιst R hR j hij)) U hcovZ
  refine ⟨j', hjj', ?_⟩
  let m : pullback f₀ (ιst R hR j' (hij.trans hjj')) ⟶
      pullback (pullback.snd f₀ (ιst R hR j hij)) (Spec.map (CommRingCat.ofHom (FGStages20.φ R j j' hjj'))) :=
    pullback.lift (trans R hR f₀ j j' hij hjj') (pullback.snd _ _) (trans_snd R hR f₀ j j' hij hjj')
  have hm : m ≫ pullback.fst _ _ = trans R hR f₀ j j' hij hjj' := pullback.lift_fst _ _ _
  rw [← hm]
  exact iSup_preimage_comp_eq_top _ _ U hcov'

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.SPKit20"

end SPD20
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.SPKit20"

end E20KIT
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.SPKit20"

section E22KIT

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.AlgebraicGeometry Opposite"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZSKit22

variable {X : Scheme.{u}} {M : X.Modules}

def sectionsOfGlobal (τ : Γ(M, ⊤)) : (M : SheafOfModules X.ringCatSheaf).sections :=
  PresheafOfModules.sectionsMk (M := M.val)
    (fun U => (M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op τ : Γ(M, U.unop)))
    (by
      intro U V i
      change M.presheaf.map i (M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op τ) = _
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl)

def homOfSection (τ : Γ(M, ⊤)) : 𝟙_ X.Modules ⟶ M :=
  (SheafOfModules.unitHomEquiv M).symm (sectionsOfGlobal τ)

theorem homOfSection_app (τ : Γ(M, ⊤)) (U : X.Opens) (r : Γ(X, U)) :
    (homOfSection τ).app U (Scheme.Modules.toUnitSection U r) =
      r • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op τ := by
  rfl

theorem homOfSection_app_one (τ : Γ(M, ⊤)) :
    (homOfSection τ).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = τ := by
  rw [homOfSection_app, one_smul]
  change (M.presheaf.map (𝟙 _)) τ = τ
  rw [M.presheaf.map_id]
  rfl

theorem app_map {N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app U x) := by
  have := (φ.mapPresheaf).naturality i.op
  exact congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, U) → Γ(N, V))) this) x

theorem map_toUnitSection_one {U V : X.Opens} (i : V ⟶ U) :
    (𝟙_ X.Modules).presheaf.map i.op (Scheme.Modules.toUnitSection U 1) = Scheme.Modules.toUnitSection V 1 := by
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
    Scheme.Modules.ofUnitSection_toUnitSection, map_one]

theorem unitHom_app (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) (r : Γ(X, U)) :
    s.app U (Scheme.Modules.toUnitSection U r) =
      r • M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) := by
  rw [← app_map, map_toUnitSection_one, ← Scheme.Modules.Hom.app_smul]
  congr 1
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection,
    Scheme.Modules.ofUnitSection_toUnitSection, mul_one]

theorem unitHom_ext {s₁ s₂ : 𝟙_ X.Modules ⟶ M}
    (h : s₁.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = s₂.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :
    s₁ = s₂ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change s₁.app U (Scheme.Modules.toUnitSection U (Scheme.Modules.ofUnitSection U m)) =
    s₂.app U (Scheme.Modules.toUnitSection U (Scheme.Modules.ofUnitSection U m))
  rw [unitHom_app s₁, unitHom_app s₂, h]

theorem homOfSection_app_one_eq (s : 𝟙_ X.Modules ⟶ M) :
    homOfSection (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) = s :=
  unitHom_ext (homOfSection_app_one _)

theorem homOfSection_comp {N : X.Modules} (τ : Γ(M, ⊤)) (φ : M ⟶ N) :
    homOfSection τ ≫ φ = homOfSection (φ.app ⊤ τ) := by
  apply unitHom_ext
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, homOfSection_app_one, homOfSection_app_one]

def nv (τ : Γ(M, ⊤)) : X.Opens :=
  (Scheme.Modules.zeroSchemeIdeal (homOfSection τ)).support.compl

theorem mem_nv_iff (τ : Γ(M, ⊤)) (x : X) :
    x ∈ nv τ ↔ x ∉ (Scheme.Modules.zeroSchemeIdeal (homOfSection τ)).support := Iff.rfl

theorem disjoint_nv (τ : Γ(M, ⊤)) :
    Disjoint (nv τ : Set X) (Scheme.Modules.zeroSchemeIdeal (homOfSection τ)).support :=
  Set.disjoint_left.2 fun _ hx hx' => hx hx'

theorem isFrameOn_nv (hM : Scheme.Modules.IsInvertible M) (τ : Γ(M, ⊤)) :
    Scheme.Modules.IsFrameOn τ (nv τ) := by
  have h := Scheme.Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal hM
    (homOfSection τ) (nv τ) (disjoint_nv τ)
  rwa [homOfSection_app_one] at h

theorem notMem_support_of_isFrameOn (hM : Scheme.Modules.IsInvertible M) (τ : Γ(M, ⊤)) {V : X.Opens}
    (hτ : Scheme.Modules.IsFrameOn τ V) {x : X} (hx : x ∈ V) :
    x ∉ (Scheme.Modules.zeroSchemeIdeal (homOfSection τ)).support := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  have hΩ : Scheme.Modules.IsFrameOn (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op τ) V := hτ.map _
  have hideal := Scheme.Modules.IsInvertible.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul hM
    (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op τ) hΩ (homOfSection τ) 1
    (by rw [homOfSection_app, one_smul]) ⟨U, hU⟩ hUV
  rw [map_one] at hideal
  intro hmem
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU, hideal,
    Scheme.mem_zeroLocus_iff] at hmem
  exact hmem 1 (Ideal.subset_span rfl) (by rw [Scheme.basicOpen_one]; exact hxU)

theorem le_nv_of_isFrameOn (hM : Scheme.Modules.IsInvertible M) (τ : Γ(M, ⊤)) {V : X.Opens}
    (hτ : Scheme.Modules.IsFrameOn τ V) : V ≤ nv τ :=
  fun _ hx => notMem_support_of_isFrameOn hM τ hτ hx

theorem ProjPresentation.preimage_basicOpen_le_nv {R : Type u} [CommRing R] {f : X ⟶ Spec (.of R)} {N : ℕ}
    (hM : Scheme.Modules.IsInvertible M) (𝔓 : M.ProjPresentation f N) (i : Fin (N + 1)) :
    𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) ≤ nv (𝔓.σ i) :=
  le_nv_of_isFrameOn hM (𝔓.σ i) (fun _ _ hWV => 𝔓.frame i _ hWV)

theorem ProjPresentation.iSup_nv_eq_top {R : Type u} [CommRing R] {f : X ⟶ Spec (.of R)} {N : ℕ}
    (hM : Scheme.Modules.IsInvertible M) (𝔓 : M.ProjPresentation f N) : (⨆ i, nv (𝔓.σ i)) = ⊤ := by
  apply top_le_iff.1
  intro x _
  have hx : 𝔓.toProj.base x ∈ (⨆ i : Fin (N + 1),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) := by
    rw [Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R N)]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ProjPresentation.preimage_basicOpen_le_nv hM 𝔓 i hi⟩

theorem IsInvertible.of_iso {M' : X.Modules} (hM : Scheme.Modules.IsInvertible M) (e : M ≅ M') :
    Scheme.Modules.IsInvertible M' := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨t⟩⟩ := hM.1 x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ t⟩⟩

theorem nv_app_of_isIso {M' : X.Modules} (φ : M ⟶ M') [IsIso φ] (τ : Γ(M, ⊤)) :
    nv (φ.app ⊤ τ) = nv τ := by
  simp only [nv, ← homOfSection_comp, Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso]

theorem nv_iso_hom_app {M' : X.Modules} (e : M ≅ M') (τ : Γ(M, ⊤)) : nv (e.hom.app ⊤ τ) = nv τ :=
  nv_app_of_isIso e.hom τ

variable {X' : Scheme.{u}}

def pbg (F : X' ⟶ X) (τ : Γ(M, ⊤)) : Γ((Scheme.Modules.pullback F).obj M, ⊤) :=
  Scheme.Modules.pullbackLocalSection F τ

theorem pbg_def (F : X' ⟶ X) (τ : Γ(M, ⊤)) :
    pbg F τ = ((Scheme.Modules.pullbackPushforwardAdjunction F).unit.app M).app ⊤ τ := rfl

theorem pbg_eq_pullbackLocalSection (F : X' ⟶ X) (τ : Γ(M, ⊤)) :
    pbg F τ = Scheme.Modules.pullbackLocalSection F τ := rfl

theorem pullbackUnitIso_inv_app_one (F : X' ⟶ X) :
    (Scheme.Modules.pullbackUnitIso F).inv.app (F ⁻¹ᵁ ⊤) (Scheme.Modules.toUnitSection (F ⁻¹ᵁ ⊤) 1) =
      Scheme.Modules.pullbackLocalSection F (Scheme.Modules.toUnitSection ⊤ 1) := by
  have h := Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection F ⊤ 1
  rw [map_one] at h
  have h' := congrArg ((Scheme.Modules.pullbackUnitIso F).inv.app (F ⁻¹ᵁ ⊤)) h
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
    Scheme.Modules.Hom.id_app, CategoryTheory.id_apply] at h'
  exact h'.symm

theorem pullbackSection_homOfSection (F : X' ⟶ X) (τ : Γ(M, ⊤)) :
    Scheme.Modules.pullbackSection F (homOfSection τ) = homOfSection (pbg F τ) := by
  apply unitHom_ext
  rw [homOfSection_app_one, Scheme.Modules.pullbackSection_def]
  have key : ((Scheme.Modules.pullback F).map (homOfSection τ)).app (F ⁻¹ᵁ ⊤)
      ((Scheme.Modules.pullbackUnitIso F).inv.app (F ⁻¹ᵁ ⊤) (Scheme.Modules.toUnitSection (F ⁻¹ᵁ ⊤) 1)) =
      Scheme.Modules.pullbackLocalSection F τ := by
    rw [pullbackUnitIso_inv_app_one, ← Scheme.Modules.pullbackLocalSection_app, homOfSection_app_one]
  exact key

theorem comap_zeroSchemeIdeal_homOfSection (hM : Scheme.Modules.IsInvertible M) (F : X' ⟶ X) (τ : Γ(M, ⊤)) :
    (Scheme.Modules.zeroSchemeIdeal (homOfSection τ)).comap F =
      Scheme.Modules.zeroSchemeIdeal (homOfSection (pbg F τ)) := by
  rw [Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal F hM, pullbackSection_homOfSection]

theorem preimage_nv (hM : Scheme.Modules.IsInvertible M) (F : X' ⟶ X) (τ : Γ(M, ⊤)) :
    F ⁻¹ᵁ nv τ = nv (pbg F τ) := by
  apply TopologicalSpace.Opens.ext
  change F.base ⁻¹' ((Scheme.Modules.zeroSchemeIdeal (homOfSection τ)).support : Set X)ᶜ =
    ((Scheme.Modules.zeroSchemeIdeal (homOfSection (pbg F τ))).support : Set X')ᶜ
  rw [← comap_zeroSchemeIdeal_homOfSection hM, Scheme.IdealSheafData.support_comap, Set.preimage_compl]
  rfl

theorem iSup_preimage_nv_eq_top {Y Xj : Scheme.{u}} {R : Type u} [CommRing R] {f : Y ⟶ Spec (.of R)} {N : ℕ}
    {M' : Y.Modules} {Mj : Xj.Modules} (hMj : Scheme.Modules.IsInvertible Mj)
    (𝔓' : M'.ProjPresentation f N) (c : Y ⟶ Xj) (t : Fin (N + 1) → Γ(Mj, ⊤))
    (e : (Scheme.Modules.pullback c).obj Mj ≅ M') (he : ∀ k, e.hom.app ⊤ (pbg c (t k)) = 𝔓'.σ k) :
    (⨆ k, c ⁻¹ᵁ nv (t k)) = ⊤ := by
  have hM' : Scheme.Modules.IsInvertible M' := IsInvertible.of_iso (hMj.pullback c) e
  have h : ∀ k, c ⁻¹ᵁ nv (t k) = nv (𝔓'.σ k) := fun k => by
    rw [preimage_nv hMj, ← he k, nv_iso_hom_app]
  simp only [h]
  exact ProjPresentation.iSup_nv_eq_top hM' 𝔓'

theorem iSup_preimage_nv_eq_top' {Y Xj : Scheme.{u}} {R : Type u} [CommRing R] {f : Y ⟶ Spec (.of R)} {N : ℕ}
    {M' : Y.Modules} {Mj : Xj.Modules} (hMj : Scheme.Modules.IsInvertible Mj)
    (𝔓' : M'.ProjPresentation f N) (c : Y ⟶ Xj) (t : Fin (N + 1) → Γ(Mj, ⊤))
    (e : (Scheme.Modules.pullback c).obj Mj ≅ M')
    (he : ∀ k, e.hom.app ⊤ ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app _).app ⊤) (t k)) = 𝔓'.σ k) :
    (⨆ k, c ⁻¹ᵁ nv (t k)) = ⊤ :=
  iSup_preimage_nv_eq_top hMj 𝔓' c t e he

theorem hframe_nv (hM : Scheme.Modules.IsInvertible M) {ι : Type*} (σ : ι → Γ(M, ⊤)) :
    ∀ (i : ι) (V : X.Opens), V ≤ nv (σ i) →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ i) : Γ(M, V)) :=
  fun i _ hV => isFrameOn_nv hM (σ i) le_top hV

theorem exists_projPresentation_of_iSup_nv_eq_top {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R))
    (hM : Scheme.Modules.IsInvertible M) (N : ℕ) (σ : Fin (N + 1) → Γ(M, ⊤)) (hU : (⨆ i, nv (σ i)) = ⊤) :
    ∃ 𝔓 : M.ProjPresentation f N, 𝔓.σ = σ ∧
      ∀ i, nv (σ i) ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) :=
  AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top f M N σ (fun i => nv (σ i)) hU
    (hframe_nv hM σ)

theorem nv_app_pbg (hM : Scheme.Modules.IsInvertible M) (r : X' ⟶ X) {M'' : X'.Modules}
    (θ : (Scheme.Modules.pullback r).obj M ≅ M'') (τ : Γ(M, ⊤)) :
    nv (θ.hom.app ⊤ (pbg r τ)) = r ⁻¹ᵁ nv τ := by
  rw [nv_iso_hom_app, preimage_nv hM]

theorem iSup_nv_app_pbg_eq_top (hM : Scheme.Modules.IsInvertible M) (r : X' ⟶ X) {M'' : X'.Modules}
    (θ : (Scheme.Modules.pullback r).obj M ≅ M'') {ι : Type*} (t : ι → Γ(M, ⊤))
    (hcov : (⨆ k, r ⁻¹ᵁ nv (t k)) = ⊤) :
    (⨆ k, nv (θ.hom.app ⊤ (pbg r (t k)))) = ⊤ := by
  simp only [nv_app_pbg hM]
  exact hcov

theorem isInvertible_of_pullback_iso (hM : Scheme.Modules.IsInvertible M) (r : X' ⟶ X) {M'' : X'.Modules}
    (θ : (Scheme.Modules.pullback r).obj M ≅ M'') : Scheme.Modules.IsInvertible M'' :=
  IsInvertible.of_iso (hM.pullback r) θ

theorem isClosedImmersion_of_comm_of_isPullback_toProj
    {T : Type} [CommRing T] {k : Type} [CommRing k] [Algebra T k] {N : ℕ}
    {Y : Scheme.{0}} (w : Y ⟶ Spec (CommRingCat.of T))
    {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (c : X ⟶ Y)
    (hc : IsPullback c p w (Spec.map (CommRingCat.ofHom (algebraMap T k))))
    (φT : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) T)) (hφT : φT ≫ ProjSpace.π T N = w)
    (φk : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)) [IsClosedImmersion φk]
    (hφk : φk ≫ ProjSpace.π k N = p)
    (hcomm : φk ≫ ProjSpace.map T k N = c ≫ φT) :
    ∀ mA : pullback (φT ≫ ProjSpace.π T N) (Spec.map (CommRingCat.ofHom (algebraMap T k))) ⟶
        pullback (ProjSpace.π T N) (Spec.map (CommRingCat.ofHom (algebraMap T k))),
      mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φT → mA ≫ pullback.snd _ _ = pullback.snd _ _ →
      IsClosedImmersion mA := by
  intro mA h1 h2
  have hc' : IsPullback c p (φT ≫ ProjSpace.π T N) (Spec.map (CommRingCat.ofHom (algebraMap T k))) := by
    rw [hφT]; exact hc
  have hV := ProjSpace.isPullback_map T k N
  have e : hc'.isoPullback.hom ≫ mA = φk ≫ hV.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, h1, ← Category.assoc, hc'.isoPullback_hom_fst, ← hcomm, Category.assoc,
        hV.isoPullback_hom_fst]
    · rw [Category.assoc, h2, hc'.isoPullback_hom_snd, Category.assoc, hV.isoPullback_hom_snd, hφk]
  have e' : mA = hc'.isoPullback.inv ≫ φk ≫ hV.isoPullback.hom := by
    rw [← e, Iso.inv_hom_id_assoc]
  rw [e']
  infer_instance

end ZSKit22
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.SPKit20"

namespace ZSKit22

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.AlgebraicGeometry.Scheme.Modules"

variable {X Y Z : Scheme.{0}}

theorem pullbackComp_inv_app_app_pbg (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ⊤ (pbg (f ≫ g) m) = pbg f (pbg g m) := by
  have h1 := CategoryTheory.unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h1
  have h2 := congrArg (fun k => Scheme.Modules.Hom.app k ⊤ m) h1
  dsimp only at h2
  erw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app] at h2
  erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h2
  exact h2.symm

theorem pullbackComp_hom_app_app_pbg (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app ⊤ (pbg f (pbg g m)) = pbg (f ≫ g) m := by
  rw [← pullbackComp_inv_app_app_pbg]
  change (((Scheme.Modules.pullbackComp f g).inv.app M) ≫ ((Scheme.Modules.pullbackComp f g).hom.app M)).app ⊤
    (pbg (f ≫ g) m) = _
  rw [Iso.inv_hom_id_app, Scheme.Modules.Hom.id_app]
  rfl

theorem pbg_app (f : X ⟶ Y) {N N' : Y.Modules} (φ : N ⟶ N') (y : Γ(N, ⊤)) :
    pbg f (φ.app ⊤ y) = ((Scheme.Modules.pullback f).map φ).app ⊤ (pbg f y) :=
  Scheme.Modules.pullbackLocalSection_app f φ y

theorem iso_inv_hom_app {N N' : X.Modules} (θ : N ≅ N') (U : X.Opens) (y : Γ(N, U)) :
    θ.inv.app U (θ.hom.app U y) = y := by
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app,
    CategoryTheory.id_apply]

def compIso (c : X ⟶ Y) (r : Y ⟶ Z) {N : Z.Modules} {N' : Y.Modules} (θ : (Scheme.Modules.pullback r).obj N ≅ N')
    {M' : X.Modules} (e₁ : (Scheme.Modules.pullback (c ≫ r)).obj N ≅ M') :
    (Scheme.Modules.pullback c).obj N' ≅ M' :=
  (Scheme.Modules.pullback c).mapIso θ.symm ≪≫ (Scheme.Modules.pullbackComp c r).app N ≪≫ e₁

theorem compIso_hom_app_pbg (c : X ⟶ Y) (r : Y ⟶ Z) {N : Z.Modules} {N' : Y.Modules}
    (θ : (Scheme.Modules.pullback r).obj N ≅ N') {M' : X.Modules} (e₁ : (Scheme.Modules.pullback (c ≫ r)).obj N ≅ M')
    (y : Γ(N, ⊤)) :
    (compIso c r θ e₁).hom.app ⊤ (pbg c (θ.hom.app ⊤ (pbg r y))) = e₁.hom.app ⊤ (pbg (c ≫ r) y) := by
  change e₁.hom.app ⊤ (((Scheme.Modules.pullbackComp c r).hom.app N).app ⊤
    (((Scheme.Modules.pullback c).map θ.inv).app ⊤ (pbg c (θ.hom.app ⊤ (pbg r y))))) = _
  rw [← pbg_app, iso_inv_hom_app, pullbackComp_hom_app_app_pbg]

end ZSKit22
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.SPKit20"

namespace SPD22

p2m_open "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.NoethBC20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.SPD20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.ZSKit22 AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.AlgebraicGeometry.Scheme.Modules"

section

variable {k : Type} [Field k] (R : Subalgebra ℤ k) (hR : R.FG)
variable {A₀ : Scheme.{0}} (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (M₀ : A₀.Modules)

def θst (j j' : FGStages20.Idx R) (hij : i₀ R hR ≤ j) (hjj' : j ≤ j') :
    (Scheme.Modules.pullback (trans R hR f₀ j j' hij hjj')).obj
        ((Scheme.Modules.pullback (pullback.fst f₀ (ιst R hR j hij))).obj M₀) ≅
      (Scheme.Modules.pullback (pullback.fst f₀ (ιst R hR j' (hij.trans hjj')))).obj M₀ :=
  (Scheme.Modules.pullbackComp (trans R hR f₀ j j' hij hjj') (pullback.fst f₀ (ιst R hR j hij))).app M₀ ≪≫
    (Scheme.Modules.pullbackCongr (trans_fst R hR f₀ j j' hij hjj')).app M₀

variable {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (gA : X ⟶ A₀)

theorem stage_tail (hg : IsPullback gA p f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    [QuasiCompact f₀] [QuasiSeparated f₀] (hM : Scheme.Modules.IsInvertible M₀)
    (j : FGStages20.Idx R) (hij : i₀ R hR ≤ j) {N : ℕ}
    (t : Fin (N + 1) → Γ((Scheme.Modules.pullback
      (pullback.fst f₀ (ιst R hR j hij))).obj M₀, ⊤))
    (𝔓' : Scheme.Modules.ProjPresentation ((Scheme.Modules.pullback gA).obj M₀) p N) [IsClosedImmersion 𝔓'.toProj]
    (hsec : ∀ (c : X ⟶ Limits.pullback f₀ (ιst R hR j hij)),
        c ≫ Limits.pullback.fst f₀ (ιst R hR j hij) = gA →
        c ≫ Limits.pullback.snd f₀ (ιst R hR j hij) =
          p ≫ Spec.map (CommRingCat.ofHom (FGStages20.g R j)) →
        ∃ e : (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback
              (Limits.pullback.fst f₀ (ιst R hR j hij))).obj M₀) ≅
            (Scheme.Modules.pullback gA).obj M₀,
          ∀ l, e.hom.app ⊤ (pbg c (t l)) = 𝔓'.σ l) :
    ∃ (T : Subalgebra ℤ k) (hRT : R ≤ T) (_ : T.FG) (N' : ℕ)
      (𝔓 : Scheme.Modules.ProjPresentation
        ((Scheme.Modules.pullback
          (pullback.fst f₀ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom)))).obj M₀)
        (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom))) N'),
      ∀ mA : pullback (𝔓.toProj ≫ ProjSpace.π ↥T N') (Spec.map (CommRingCat.ofHom (algebraMap ↥T k))) ⟶
          pullback (ProjSpace.π ↥T N') (Spec.map (CommRingCat.ofHom (algebraMap ↥T k))),
        mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔓.toProj → mA ≫ pullback.snd _ _ = pullback.snd _ _ →
        IsClosedImmersion mA := by
  haveI : Nonempty (FGStages20.Idx R) := FGStages20.nonempty R hR

  obtain ⟨e, he⟩ := hsec (cst R hR f₀ p gA hg j hij)
    (bcComparison_fst (ιst R hR j hij) p _ _ (specLeg_ιst R hR j hij) gA hg)
    (bcComparison_snd (ιst R hR j hij) p _ _ (specLeg_ιst R hR j hij) gA hg)
  have hMj : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (pullback.fst f₀ (ιst R hR j hij))).obj M₀) := hM.pullback _
  have hcov : (⨆ l, (cst R hR f₀ p gA hg j hij) ⁻¹ᵁ nv (t l)) = ⊤ :=
    iSup_preimage_nv_eq_top' hMj 𝔓' (cst R hR f₀ p gA hg j hij) t e he

  obtain ⟨j', hjj', hcov'⟩ := exists_stage_cover R hR f₀ p gA hg j hij (fun l => nv (t l)) hcov

  have hMj' : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (pullback.fst f₀ (ιst R hR j' (hij.trans hjj')))).obj M₀) := hM.pullback _
  have hU' : (⨆ l, nv ((θst R hR f₀ M₀ j j' hij hjj').hom.app ⊤ (pbg (trans R hR f₀ j j' hij hjj') (t l)))) = ⊤ :=
    iSup_nv_app_pbg_eq_top hMj (trans R hR f₀ j j' hij hjj') (θst R hR f₀ M₀ j j' hij hjj') t hcov'
  obtain ⟨𝔓, h𝔓σ, -⟩ := exists_projPresentation_of_iSup_nv_eq_top (pullback.snd f₀ (ιst R hR j' (hij.trans hjj')))
    hMj' N (fun l => (θst R hR f₀ M₀ j j' hij hjj').hom.app ⊤ (pbg (trans R hR f₀ j j' hij hjj') (t l))) hU'

  have hc' : IsPullback (cst R hR f₀ p gA hg j' (hij.trans hjj')) p (pullback.snd f₀ (ιst R hR j' (hij.trans hjj')))
      (Spec.map (CommRingCat.ofHom (algebraMap ↥j'.1 k))) :=
    isPullback_bcComparison (ιst R hR j' (hij.trans hjj')) p _ _ (specLeg_ιst R hR j' (hij.trans hjj')) gA hg
  obtain ⟨𝔓k, hσk, hcommk, -⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback (R := ↥j'.1) (A := k) hc' 𝔓

  obtain ⟨e₁, he₁⟩ := hsec (cst R hR f₀ p gA hg j' (hij.trans hjj') ≫ trans R hR f₀ j j' hij hjj')
    (by rw [cst_trans]; exact bcComparison_fst (ιst R hR j hij) p _ _ (specLeg_ιst R hR j hij) gA hg)
    (by rw [cst_trans]; exact bcComparison_snd (ιst R hR j hij) p _ _ (specLeg_ιst R hR j hij) gA hg)
  obtain ⟨𝔓'', h𝔓''π, h𝔓''σ⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso 𝔓k
    (compIso (cst R hR f₀ p gA hg j' (hij.trans hjj')) (trans R hR f₀ j j' hij hjj') (θst R hR f₀ M₀ j j' hij hjj') e₁)
  have hσ'' : ∀ i, 𝔓''.σ i = 𝔓'.σ i := fun i => by
    rw [h𝔓''σ, hσk, ← he₁ i, h𝔓σ]
    exact compIso_hom_app_pbg _ _ _ e₁ (t i)
  have heq : 𝔓''.toProj = 𝔓'.toProj :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq 𝔓'' 𝔓' hσ''
  haveI : IsClosedImmersion 𝔓k.toProj := by rw [← h𝔓''π, heq]; infer_instance

  exact ⟨j'.1, j'.2.2, j'.2.1, N, 𝔓,
    isClosedImmersion_of_comm_of_isPullback_toProj (pullback.snd f₀ (ιst R hR j' (hij.trans hjj'))) p
      (cst R hR f₀ p gA hg j' (hij.trans hjj')) hc' 𝔓.toProj 𝔓.toProj_π 𝔓k.toProj 𝔓k.toProj_π hcommk⟩

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.SPKit20"

end SPD22
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.SPKit20"

end E22KIT
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.SPKit20"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme"

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {g d n : ℕ} {k : Type} [Field k] (u : PolarisedAbelianScheme g d n k)
    (σ : SchemeHomOver u.f u.f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t u.f),
      NeronModelInfra.schemeHomOverComp (u.L.mul t x y) σ =
        u.L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (hpol : ∀ s : ↥(Spec (CommRingCat.of k)), ∃ U : (Spec (CommRingCat.of k)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj u.pol) ≅
        (Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj u.pol)) :
    ∃ (R : Subalgebra ℤ k) (_ : R.FG)
      (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥R)) (L₀ : RelativeGroupLaw ↥R f₀)
      (_ : AbelianSchemePropertyBundle ↥R f₀)
      (_ : GeometricallyConnected f₀)
      (M₀ : A₀.Modules) (_ : Scheme.Modules.IsInvertible M₀)
      (σ₀ : SchemeHomOver f₀ f₀) (_ : IsIso σ₀.1)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥R)) (x y : SchemeHomOver t f₀),
        NeronModelInfra.schemeHomOverComp (L₀.mul t x y) σ₀ =
          L₀.mul t (NeronModelInfra.schemeHomOverComp x σ₀) (NeronModelInfra.schemeHomOverComp y σ₀))
      (_ : ∀ s : ↥(Spec (CommRingCat.of ↥R)), ∃ U : (Spec (CommRingCat.of ↥R)).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (f₀ ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ₀.1).obj M₀) ≅
          (Scheme.Modules.pullback (f₀ ⁻¹ᵁ U).ι).obj M₀))
      (gA : u.A ⟶ A₀) (hg : CategoryTheory.IsPullback gA u.f f₀ (Spec.map (CommRingCat.ofHom R.val.toRingHom))),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t u.f),
        (u.L.mul t x y).1 ≫ gA =
          (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom))
            ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
      Nonempty ((Scheme.Modules.pullback gA).obj M₀ ≅ u.pol) ∧
      σ.1 ≫ gA = gA ≫ σ₀.1 ∧
      ∃ (T : Subalgebra ℤ k) (hRT : R ≤ T) (_ : T.FG) (N : ℕ)
        (𝔓 : Scheme.Modules.ProjPresentation
          ((Scheme.Modules.pullback
            (pullback.fst f₀ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom)))).obj M₀)
          (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom))) N),
        ∀ mA : pullback (𝔓.toProj ≫ ProjSpace.π ↥T N) (Spec.map (CommRingCat.ofHom (algebraMap ↥T k))) ⟶
            pullback (ProjSpace.π ↥T N) (Spec.map (CommRingCat.ofHom (algebraMap ↥T k))),
          mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔓.toProj → mA ≫ pullback.snd _ _ = pullback.snd _ _ →
          IsClosedImmersion mA := by
  obtain ⟨R, hR, A₀, f₀, L₀, hb, hgc, M₀, hM, σ₀, hσiso, hσ₀, hpol₀, gA, hg, hmulc, hmod, hσc⟩ :=
    AlgebraicGeometry.PolarisedAbelianScheme.exists_fg_subalgebra_abelianScheme_pullback_iso_comp_eq_comp_of_isIso_of_pullback_pol_iso
      u σ hσiso hσ hpol
  obtain ⟨epol⟩ := hmod
  haveI := hb.proper
  haveI : Nonempty (FGStages20.Idx R) := FGStages20.nonempty R hR

  obtain ⟨N, 𝔓k, hci⟩ := u.pol_veryAmple
  obtain ⟨𝔓', h𝔓'π, h𝔓'σ⟩ := AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso 𝔓k epol.symm
  haveI : IsClosedImmersion 𝔓'.toProj := by rw [h𝔓'π]; exact hci

  obtain ⟨j, hij, t, hsec⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_unit_eq_of_isDirectLimit
      (FGStages20.φ R) (FGStages20.g R) (FGStages20.isDirectLimit R hR) (⟨R, hR, le_rfl⟩ : FGStages20.Idx R)
      f₀ gA u.f hg M₀ hM 𝔓'.σ

  obtain ⟨T, hRT, hT, N', 𝔓, hA⟩ := SPD22.stage_tail R hR f₀ M₀ u.f gA hg hM j hij t 𝔓' hsec
  exact ⟨R, hR, A₀, f₀, L₀, hb, hgc, M₀, hM, σ₀, hσiso, hσ₀, hpol₀, gA, hg, hmulc, ⟨epol⟩, hσc, T, hRT, hT, N', 𝔓, hA⟩

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.FGStages20 P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso.SPKit20"

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_projPresentation_pullback_isClosedImmersion_of_pullback_pol_iso (solution)
