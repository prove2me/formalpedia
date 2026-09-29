-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_translate_comp_eq_iff_map_eq_bot_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/31d02597-254b-554d-99a4-c79b08c07f31

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ThetaReframe
import Definitions.Def_AlgebraicGeometry_ProjSpaceLinMap
import Theorems.Thm_AlgebraicGeometry_exists_ideal_fg_forall_pullback_fst_comp_eq_iff_map_eq_bot_of_isProper_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_comp_linMap_of_sigma_eq_sum_smul
import Theorems.Thm_AlgebraicGeometry_ProjSpace_linMap_map_comp_map
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isReframe
import Theorems.Thm_AlgebraicGeometry_ProjSpace_flat_pi
import Theorems.Thm_AlgebraicGeometry_ProjSpace_locallyOfFinitePresentation_pi
import Theorems.Thm_AlgebraicGeometry_Polarisation_exists_isIso_comp_fst_comp_fst_eq_and_translate_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_ideal_fg_forall_isPullback_translate_comp_eq_iff_map_eq_bot_of_section
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.HilbertFunctor.Point.mk.injEq AlgebraicGeometry.HilbertFunctor.Point.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem solution
    {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hU : IsUnit U) (x₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) X.f) :
    ∃ J : Ideal S, J.FG ∧ ∀ (T : Type) [CommRing T] (φ : S →+* T) (Y : FramedPolarisedAbelianScheme g N n T),
      FramedPolarisedAbelianScheme.IsPullback φ X Y →
      ∀ (P' : Scheme.Modules.ProjPresentation Y.pol Y.f N),
        (∀ i : Fin (N + 1), P'.σ i =
          ∑ j : Fin (N + 1), ((Y.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (φ (U i j)))) • Y.frame.σ j) →
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) Y.f,
          (letI : Algebra S T := φ.toAlgebra;
            x.1 ≫ Y.frame.toProj ≫ ProjSpace.map S T N = Spec.map (CommRingCat.ofHom φ) ≫ x₀.1 ≫ X.frame.toProj) →
          (Polarisation.translate Y.f Y.L (𝟙 (Spec (CommRingCat.of T))) x ≫ pullback.fst Y.f (𝟙 (Spec (CommRingCat.of T))) ≫ Y.frame.toProj =
              pullback.fst Y.f (𝟙 (Spec (CommRingCat.of T))) ≫ P'.toProj ↔
            J.map φ = ⊥) := by
  classical
  haveI hsm : Smooth X.f := X.bundle.smooth
  haveI hpr : IsProper X.f := X.bundle.proper

  obtain ⟨XU, PX, hc1, hb1, hXUeq, hPXσ⟩ := AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isReframe X U hU
  have hPXproj : PX.toProj = X.frame.toProj ≫ ProjSpace.linMap S N U hU :=
    Scheme.Modules.ProjPresentation.toProj_eq_comp_linMap_of_sigma_eq_sum_smul X.frame PX U hU hPXσ

  obtain ⟨LP, 𝔓P, h𝔓P, hloc⟩ := AlgebraicGeometry.ProjSpace.exists_projPresentation_toProj_eq_and_locallyTrivial
    (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)))
  have hP₁ : Scheme.Modules.IsInvertible LP := ⟨hloc⟩
  have hP₂ : Scheme.Modules.ClosedImmersionBySections LP
      (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)) ≫ ProjSpace.π S N) :=
    ⟨N, 𝔓P, by rw [h𝔓P]; infer_instance⟩
  haveI : IsSeparated (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)) ≫ ProjSpace.π S N) := by
    rw [Category.id_comp]; infer_instance
  haveI : Flat (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)) ≫ ProjSpace.π S N) := by
    rw [Category.id_comp]; exact AlgebraicGeometry.ProjSpace.flat_pi S N
  haveI : LocallyOfFinitePresentation (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)) ≫ ProjSpace.π S N) := by
    rw [Category.id_comp]; exact AlgebraicGeometry.ProjSpace.locallyOfFinitePresentation_pi S N

  haveI : IsIso (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) := inferInstance
  let u : X.A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) :=
    inv (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ≫ Polarisation.translate X.f X.L (𝟙 _) x₀ ≫
      pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫ X.frame.toProj
  have hpr1 : pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫ X.f = pullback.snd X.f (𝟙 _) := by
    rw [pullback.condition, Category.comp_id]
  have hu : u ≫ (𝟙 _ ≫ ProjSpace.π S N) = X.f := by
    simp only [u, Category.id_comp, Category.assoc, X.frame.toProj_π]
    rw [hpr1, Polarisation.translate_snd, ← hpr1, IsIso.inv_hom_id_assoc]
  have hv : PX.toProj ≫ (𝟙 _ ≫ ProjSpace.π S N) = X.f := by rw [Category.id_comp, PX.toProj_π]
  obtain ⟨J, hJfg, hJ⟩ :=
    AlgebraicGeometry.exists_ideal_fg_forall_pullback_fst_comp_eq_iff_map_eq_bot_of_isProper_of_flat S X.f
      (𝟙 _ ≫ ProjSpace.π S N) X.pol X.pol_isInvertible X.pol_veryAmple LP hP₁ hP₂ u PX.toProj hu hv
  refine ⟨J, hJfg, fun T _ φ Y hY P' hP'σ x hpin => ?_⟩
  rw [← hJ T φ]
  obtain ⟨gA, hg, hmul, hP, ⟨ιpol⟩, hproj⟩ := id hY
  letI : Algebra S T := φ.toAlgebra

  have hUφ : IsUnit (U.map (algebraMap S T)) := hU.map (algebraMap S T).mapMatrix
  have hP'proj : P'.toProj = Y.frame.toProj ≫ ProjSpace.linMap T N (U.map (algebraMap S T)) hUφ :=
    Scheme.Modules.ProjPresentation.toProj_eq_comp_linMap_of_sigma_eq_sum_smul Y.frame P' (U.map (algebraMap S T)) hUφ
      (fun i => by rw [hP'σ i]; rfl)
  have hBC : P'.toProj ≫ ProjSpace.map S T N = gA ≫ PX.toProj := by
    rw [hP'proj, hPXproj, Category.assoc, AlgebraicGeometry.ProjSpace.linMap_map_comp_map (R := S) (A := T) N U hU hUφ,
      ← Category.assoc, hproj, Category.assoc]

  haveI := X.frame_isClosedImmersion
  have hx : x.1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ x₀.1 := by
    rw [← cancel_mono X.frame.toProj, Category.assoc, Category.assoc, ← hproj]
    simpa only [Category.assoc] using hpin
  obtain ⟨κ, -, hκ1, hκ2⟩ := AlgebraicGeometry.Polarisation.exists_isIso_comp_fst_comp_fst_eq_and_translate_comp_eq_of_isPullback φ X.L Y.L gA hg hmul x₀ x hx

  set μ := κ ≫ pullback.fst (pullback.snd X.f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) with hμ
  have hμ1 : μ ≫ pullback.fst X.f (𝟙 _) = pullback.fst Y.f (𝟙 _) ≫ gA := by rw [hμ, Category.assoc, hκ1]
  have hμ2 : Polarisation.translate Y.f Y.L (𝟙 _) x ≫ μ = μ ≫ Polarisation.translate X.f X.L (𝟙 _) x₀ := by
    rw [hμ]; simpa only [Category.assoc] using hκ2

  let κ' : pullback Y.f (𝟙 (Spec (CommRingCat.of T))) ⟶ pullback X.f (Spec.map (CommRingCat.ofHom φ)) :=
    pullback.fst Y.f (𝟙 _) ≫ hg.isoPullback.hom
  have hκ' : κ' ≫ pullback.fst X.f (Spec.map (CommRingCat.ofHom φ)) = pullback.fst Y.f (𝟙 _) ≫ gA := by
    simp only [κ', Category.assoc, IsPullback.isoPullback_hom_fst]
  haveI : IsIso (pullback.fst Y.f (𝟙 (Spec (CommRingCat.of T)))) := inferInstance
  haveI : Epi κ' := by simp only [κ']; infer_instance

  have e1 : κ' ≫ pullback.fst X.f (Spec.map (CommRingCat.ofHom φ)) ≫ u =
      Polarisation.translate Y.f Y.L (𝟙 _) x ≫ pullback.fst Y.f (𝟙 _) ≫ Y.frame.toProj ≫ ProjSpace.map S T N := by
    calc κ' ≫ pullback.fst X.f (Spec.map (CommRingCat.ofHom φ)) ≫ u
        = (κ' ≫ pullback.fst X.f (Spec.map (CommRingCat.ofHom φ))) ≫
            inv (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ≫ Polarisation.translate X.f X.L (𝟙 _) x₀ ≫
              pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫ X.frame.toProj := by
          simp only [u, Category.assoc]
      _ = (μ ≫ pullback.fst X.f (𝟙 _)) ≫
            inv (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ≫ Polarisation.translate X.f X.L (𝟙 _) x₀ ≫
              pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫ X.frame.toProj := by rw [hκ', hμ1]
      _ = (Polarisation.translate Y.f Y.L (𝟙 _) x ≫ μ) ≫
              pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))) ≫ X.frame.toProj := by
          rw [hμ2]; simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      _ = Polarisation.translate Y.f Y.L (𝟙 _) x ≫ (μ ≫ pullback.fst X.f (𝟙 _)) ≫ X.frame.toProj := by
          simp only [Category.assoc]
      _ = Polarisation.translate Y.f Y.L (𝟙 _) x ≫ pullback.fst Y.f (𝟙 _) ≫ Y.frame.toProj ≫ ProjSpace.map S T N := by
          rw [hμ1, hproj]; simp only [Category.assoc]
  have e2 : κ' ≫ pullback.fst X.f (Spec.map (CommRingCat.ofHom φ)) ≫ PX.toProj =
      pullback.fst Y.f (𝟙 _) ≫ P'.toProj ≫ ProjSpace.map S T N := by
    rw [← Category.assoc, hκ', Category.assoc, ← hBC]
  constructor
  · intro H
    apply (cancel_epi κ').mp
    rw [e1, e2]
    simpa only [Category.assoc] using congrArg (· ≫ ProjSpace.map S T N) H
  · intro H'
    apply (AlgebraicGeometry.ProjSpace.isPullback_map S T N).hom_ext
    · have := congrArg (fun k => κ' ≫ k) H'
      simp only [e1, e2] at this
      simpa only [Category.assoc] using this
    · simp only [Category.assoc, Y.frame.toProj_π, P'.toProj_π]
      rw [pullback.condition, Category.comp_id, Polarisation.translate_snd]

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_ideal_fg_forall_isPullback_translate_comp_eq_iff_map_eq_bot_of_section
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_ideal_fg_forall_isPullback_translate_comp_eq_iff_map_eq_bot_of_section (solution)
