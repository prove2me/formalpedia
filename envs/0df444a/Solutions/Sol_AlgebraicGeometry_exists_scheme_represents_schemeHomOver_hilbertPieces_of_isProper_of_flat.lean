-- Prove2me | solution 1 for AlgebraicGeometry.exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/29c7ec96-8c90-5ab0-a1a5-9c3c177b78f9

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd
import Theorems.Thm_AlgebraicGeometry_exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat
import Theorems.Thm_AlgebraicGeometry_exists_isOpen_quasiCompact_inclusion_mem_iff_isIso_fibre_of_isProper_of_flat
import Theorems.Thm_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point
import Theorems.Thm_AlgebraicGeometry_range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.HilbertFunctor.Point.mk.injEq AlgebraicGeometry.HilbertFunctor.Point.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
p2m_open "CategoryTheory.MonoidalCategory"

noncomputable section

namespace MorRepAsm

variable {S : Type} [CommRing S] {X Y : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of S))

abbrev fW : pullback f g ⟶ Spec (CommRingCat.of S) := pullback.fst f g ≫ f

section Graph

variable {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of S))

def prX : pullback (fW f g) s ⟶ pullback f s :=
  pullback.map (fW f g) s f s (pullback.fst f g) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)] theorem prX_fst : prX f g s ≫ pullback.fst f s = pullback.fst (fW f g) s ≫ pullback.fst f g := by
  rw [prX, pullback.lift_fst]

@[reassoc (attr := simp)] theorem prX_snd : prX f g s ≫ pullback.snd f s = pullback.snd (fW f g) s := by
  rw [prX, pullback.lift_snd, Category.comp_id]

scoped instance isSeparated_prX [IsSeparated g] : IsSeparated (prX f g s) :=
  MorphismProperty.pullbackMap (P := @IsSeparated) (inferInstance : IsSeparated (pullback.fst f g))
    (inferInstance : IsSeparated (𝟙 _)) rfl (Category.id_comp s).symm

variable (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s)

def graph : pullback f s ⟶ pullback (fW f g) s :=
  pullback.lift (pullback.lift (pullback.fst f s) φ (by rw [hφ]; exact pullback.condition)) (pullback.snd f s)
    (by rw [← Category.assoc, pullback.lift_fst]; exact pullback.condition)

@[reassoc (attr := simp)] theorem graph_fst_fst : graph f g s φ hφ ≫ pullback.fst (fW f g) s ≫ pullback.fst f g = pullback.fst f s := by
  rw [graph, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]

@[reassoc (attr := simp)] theorem graph_fst_snd : graph f g s φ hφ ≫ pullback.fst (fW f g) s ≫ pullback.snd f g = φ := by
  rw [graph, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]

@[reassoc (attr := simp)] theorem graph_snd : graph f g s φ hφ ≫ pullback.snd (fW f g) s = pullback.snd f s := by
  rw [graph, pullback.lift_snd]

@[reassoc (attr := simp)] theorem graph_prX : graph f g s φ hφ ≫ prX f g s = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, prX_fst, graph_fst_fst, Category.id_comp]
  · rw [Category.assoc, prX_snd, graph_snd, Category.id_comp]

theorem isClosedImmersion_graph [IsSeparated g] : IsClosedImmersion (graph f g s φ hφ) := by
  haveI : IsClosedImmersion (graph f g s φ hφ ≫ prX f g s) := by rw [graph_prX]; infer_instance
  exact IsClosedImmersion.of_comp (graph f g s φ hφ) (prX f g s)

theorem flat_graph [Flat f] : Flat (graph f g s φ hφ ≫ pullback.snd (fW f g) s) := by
  rw [graph_snd]; infer_instance

theorem lfp_graph [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (graph f g s φ hφ ≫ pullback.snd (fW f g) s) := by
  rw [graph_snd]; infer_instance

theorem eq_of_iso_graph {φ φ' : pullback f s ⟶ Y} {hφ : φ ≫ g = pullback.snd f s ≫ s} {hφ' : φ' ≫ g = pullback.snd f s ≫ s}
    (e : pullback f s ≅ pullback f s) (he : e.hom ≫ graph f g s φ' hφ' = graph f g s φ hφ) : φ = φ' := by
  have h1 : e.hom = 𝟙 _ := by
    have := congrArg (fun k => k ≫ prX f g s) he
    simpa only [Category.assoc, graph_prX, Category.comp_id] using this
  rw [h1, Category.id_comp] at he
  rw [← graph_fst_snd f g s φ hφ, ← graph_fst_snd f g s φ' hφ', he]

theorem exists_graph_of_isIso {Z : Scheme.{0}} (ι : Z ⟶ pullback (fW f g) s) [IsIso (ι ≫ prX f g s)] :
    ∃ (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s) (e : Z ≅ pullback f s),
      e.hom = ι ≫ prX f g s ∧ e.hom ≫ graph f g s φ hφ = ι := by
  let e : Z ≅ pullback f s := asIso (ι ≫ prX f g s)
  have he : e.hom = ι ≫ prX f g s := rfl
  have h1 : ι ≫ pullback.snd (fW f g) s = e.hom ≫ pullback.snd f s := by
    rw [he, Category.assoc, prX_snd]
  have hc : pullback.fst (fW f g) s ≫ pullback.fst f g ≫ f = pullback.snd (fW f g) s ≫ s := pullback.condition
  have hφ : (e.inv ≫ ι ≫ pullback.fst (fW f g) s ≫ pullback.snd f g) ≫ g = pullback.snd f s ≫ s := by
    simp only [Category.assoc]
    rw [← pullback.condition (f := f) (g := g), hc, ← Category.assoc ι, h1, Category.assoc, e.inv_hom_id_assoc]
  refine ⟨e.inv ≫ ι ≫ pullback.fst (fW f g) s ≫ pullback.snd f g, hφ, e, he, ?_⟩
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, graph_fst_fst]
      rw [← prX_fst, ← Category.assoc, ← he]
    · simp only [Category.assoc, graph_fst_snd, Iso.hom_inv_id_assoc]
  · simp only [Category.assoc, graph_snd]
    exact h1.symm

end Graph

section BC

variable {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
  (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
  (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')

def bc : pullback f s'' ⟶ pullback f s :=
  pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
    (by rw [Category.assoc, hs]; exact pullback.condition)

theorem isPullback_bc : IsPullback (bc f ψ s s'' hs) (pullback.snd f s'') (pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) := by
  have big : IsPullback (bc f ψ s s'' hs ≫ pullback.fst f s) (pullback.snd f s'') f (Spec.map (CommRingCat.ofHom ψ) ≫ s) := by
    rw [bc, pullback.lift_fst, hs]; exact IsPullback.of_hasPullback f s''
  exact big.of_right (by rw [bc, pullback.lift_snd]) (IsPullback.of_hasPullback f s)

theorem graph_bc (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s)
    (hφ'' : (bc f ψ s s'' hs ≫ φ) ≫ g = pullback.snd f s'' ≫ s'') :
    graph f g s'' (bc f ψ s s'' hs ≫ φ) hφ'' ≫
        pullback.map (fW f g) s'' (fW f g) s (𝟙 _) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
          (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs]) =
      bc f ψ s s'' hs ≫ graph f g s φ hφ := by
  delta pullback.map
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id]
    apply pullback.hom_ext
    · simp only [Category.assoc, graph_fst_fst, bc, pullback.lift_fst]
    · simp only [Category.assoc, graph_fst_snd]
  · rw [Category.assoc, pullback.lift_snd]
    simp only [Category.assoc, graph_snd, bc, pullback.lift_snd, graph_snd_assoc]

theorem bc_comp_w (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s) :
    (bc f ψ s s'' hs ≫ φ) ≫ g = pullback.snd f s'' ≫ s'' := by
  rw [Category.assoc, hφ, ← Category.assoc, bc, pullback.lift_snd, Category.assoc, hs]

end BC

section Main

variable [IsSeparated g] [Flat f] [LocallyOfFinitePresentation f]
  {Hilb : Scheme.{0}} (πH : Hilb ⟶ Spec (CommRingCat.of S))
  (ptH : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (Z : Scheme.{0}) (ι : Z ⟶ pullback (fW f g) s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd (fW f g) s) →
      LocallyOfFinitePresentation (ι ≫ pullback.snd (fW f g) s) → SchemeHomOver s πH)

def NatH : Prop :=
  ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
    (Z : Scheme.{0}) (ι : Z ⟶ pullback (fW f g) s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd (fW f g) s))
    (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd (fW f g) s))
    (Z'' : Scheme.{0}) (ι'' : Z'' ⟶ pullback (fW f g) s'') (hι'' : IsClosedImmersion ι'')
    (hfl'' : Flat (ι'' ≫ pullback.snd (fW f g) s''))
    (hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd (fW f g) s''))
    (e : Z'' ⟶ Z),
    IsPullback e (ι'' ≫ pullback.snd (fW f g) s'') (ι ≫ pullback.snd (fW f g) s) (Spec.map (CommRingCat.ofHom ψ)) →
    ι'' ≫ pullback.map (fW f g) s'' (fW f g) s (𝟙 _) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
        (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs]) = e ≫ ι →
    (ptH S'' s'' Z'' ι'' hι'' hfl'' hfp'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptH S' s Z ι hι hfl hfp).1

def SurjH : Prop :=
  ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πH),
    ∃ (Z : Scheme.{0}) (ι : Z ⟶ pullback (fW f g) s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd (fW f g) s))
      (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd (fW f g) s)),
      ptH S' s Z ι hι hfl hfp = x

def InjH : Prop :=
  ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (Z Z' : Scheme.{0}) (ι : Z ⟶ pullback (fW f g) s) (ι' : Z' ⟶ pullback (fW f g) s)
    (hι : IsClosedImmersion ι) (hι' : IsClosedImmersion ι')
    (hfl : Flat (ι ≫ pullback.snd (fW f g) s)) (hfl' : Flat (ι' ≫ pullback.snd (fW f g) s))
    (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd (fW f g) s))
    (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd (fW f g) s)),
    ptH S' s Z ι hι hfl hfp = ptH S' s Z' ι' hι' hfl' hfp' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι

variable {𝒵 : Scheme.{0}} (ι𝒵 : 𝒵 ⟶ pullback (fW f g) πH)

def UnivZ : Prop :=
  ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (Z : Scheme.{0}) (ιZ : Z ⟶ pullback (fW f g) s) (hι : IsClosedImmersion ιZ) (hfl : Flat (ιZ ≫ pullback.snd (fW f g) s))
    (hfp : LocallyOfFinitePresentation (ιZ ≫ pullback.snd (fW f g) s)),
    ∃ e : Z ⟶ 𝒵,
      IsPullback e (ιZ ≫ pullback.snd (fW f g) s) (ι𝒵 ≫ pullback.snd (fW f g) πH) (ptH S' s Z ιZ hι hfl hfp).1 ∧
      ιZ ≫ pullback.map (fW f g) s (fW f g) πH (𝟙 _) (ptH S' s Z ιZ hι hfl hfp).1 (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (ptH S' s Z ιZ hι hfl hfp).2]) = e ≫ ι𝒵

variable (U : Hilb.Opens)

def ULocus : Prop :=
  ∀ {T Z X' : Scheme.{0}} (t : T ⟶ Hilb)
    (pZ : Z ⟶ T) (eZ : Z ⟶ 𝒵) (_ : IsPullback eZ pZ (ι𝒵 ≫ pullback.snd (fW f g) πH) t)
    (qX : X' ⟶ T) (eX : X' ⟶ pullback f πH) (_ : IsPullback eX qX (pullback.snd f πH) t)
    (φ : Z ⟶ X') (_ : φ ≫ qX = pZ) (_ : φ ≫ eX = eZ ≫ (ι𝒵 ≫ prX f g πH)),
    Set.range t.base ⊆ (U : Set Hilb) ↔ IsIso φ

def mX {S' : Type} [CommRing S'] {s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver s πH) :
    pullback f s ⟶ pullback f πH :=
  pullback.map f s f πH (𝟙 X) x.1 (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, x.2])

theorem isPullback_mX {S' : Type} [CommRing S'] {s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)}
    (x : SchemeHomOver s πH) : IsPullback (mX f πH x) (pullback.snd f s) (pullback.snd f πH) x.1 := by
  have big : IsPullback (mX f πH x ≫ pullback.fst f πH) (pullback.snd f s) f (x.1 ≫ πH) := by
    rw [mX, pullback.lift_fst, Category.comp_id, x.2]; exact IsPullback.of_hasPullback f s
  exact big.of_right (by rw [mX, pullback.lift_snd]) (IsPullback.of_hasPullback f πH)

theorem prX_comp_mX {S' : Type} [CommRing S'] {s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)}
    (x : SchemeHomOver s πH) :
    prX f g s ≫ mX f πH x =
      pullback.map (fW f g) s (fW f g) πH (𝟙 _) x.1 (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, x.2]) ≫ prX f g πH := by
  apply pullback.hom_ext
  · rw [Category.assoc, mX, pullback.lift_fst, ← Category.assoc, prX_fst, Category.comp_id, Category.assoc, prX_fst,
      ← Category.assoc, pullback.lift_fst, Category.comp_id]
  · rw [Category.assoc, mX, pullback.lift_snd, ← Category.assoc, prX_snd, Category.assoc, prX_snd, pullback.lift_snd]

variable {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
  (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s)

def xH : SchemeHomOver s πH :=
  ptH S' s (pullback f s) (graph f g s φ hφ) (isClosedImmersion_graph f g s φ hφ) (flat_graph f g s φ hφ) (lfp_graph f g s φ hφ)

include U in
theorem range_xH_subset (huniv : UnivZ f g πH ptH ι𝒵) (hUL : ULocus f g πH ι𝒵 U) :
    Set.range (xH f g πH ptH s φ hφ).1.base ⊆ (U : Set Hilb) := by
  obtain ⟨e, hpb, hcompat⟩ := huniv S' s (pullback f s) (graph f g s φ hφ) (isClosedImmersion_graph f g s φ hφ)
    (flat_graph f g s φ hφ) (lfp_graph f g s φ hφ)
  refine (hUL (xH f g πH ptH s φ hφ).1 _ e hpb (pullback.snd f s) (mX f πH (xH f g πH ptH s φ hφ))
    (isPullback_mX f πH _) (graph f g s φ hφ ≫ prX f g s) ?_ ?_).mpr ?_
  · rw [Category.assoc, prX_snd]
  · rw [Category.assoc, prX_comp_mX, ← Category.assoc]
    exact congrArg (fun k => k ≫ prX f g πH) hcompat
  · rw [graph_prX]; infer_instance

def ptM (huniv : UnivZ f g πH ptH ι𝒵) (hUL : ULocus f g πH ι𝒵 U) : SchemeHomOver s (U.ι ≫ πH) :=
  ⟨IsOpenImmersion.lift U.ι (xH f g πH ptH s φ hφ).1
      (by rw [Scheme.Opens.range_ι]; exact range_xH_subset f g πH ptH ι𝒵 U s φ hφ huniv hUL), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact (xH f g πH ptH s φ hφ).2⟩

theorem ptM_ι (huniv : UnivZ f g πH ptH ι𝒵) (hUL : ULocus f g πH ι𝒵 U) :
    (ptM f g πH ptH ι𝒵 U s φ hφ huniv hUL).1 ≫ U.ι = (xH f g πH ptH s φ hφ).1 :=
  IsOpenImmersion.lift_fac _ _ _

end Main

end MorRepAsm
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm"

namespace MorRepAsm

variable {S : Type} [CommRing S] {X Y : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of S))

section Clauses

variable [IsSeparated g] [Flat f] [LocallyOfFinitePresentation f]
  {Hilb : Scheme.{0}} (πH : Hilb ⟶ Spec (CommRingCat.of S))
  (ptH : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (Z : Scheme.{0}) (ι : Z ⟶ pullback (fW f g) s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd (fW f g) s) →
      LocallyOfFinitePresentation (ι ≫ pullback.snd (fW f g) s) → SchemeHomOver s πH)
  {𝒵 : Scheme.{0}} (ι𝒵 : 𝒵 ⟶ pullback (fW f g) πH) (U : Hilb.Opens)
  (huniv : UnivZ f g πH ptH ι𝒵) (hUL : ULocus f g πH ι𝒵 U)

include huniv hUL

theorem natM (hnat : NatH f g πH ptH)
    (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
    (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s) :
    (ptM f g πH ptH ι𝒵 U s'' (bc f ψ s s'' hs ≫ φ) (bc_comp_w f g ψ s s'' hs φ hφ) huniv hUL).1 =
      Spec.map (CommRingCat.ofHom ψ) ≫ (ptM f g πH ptH ι𝒵 U s φ hφ huniv hUL).1 := by
  rw [← cancel_mono U.ι, Category.assoc, ptM_ι, ptM_ι]
  refine hnat S' S'' ψ s s'' hs (pullback f s) (graph f g s φ hφ) _ _ _ (pullback f s'') (graph f g s'' _ _) _ _ _
    (bc f ψ s s'' hs) ?_ (graph_bc f g ψ s s'' hs φ hφ _)
  rw [graph_snd, graph_snd]
  exact isPullback_bc f ψ s s'' hs

theorem surjM (hnat : NatH f g πH ptH) (hsurj : SurjH f g πH ptH)
    (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver s (U.ι ≫ πH)) :
    ∃ (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s), ptM f g πH ptH ι𝒵 U s φ hφ huniv hUL = x := by
  obtain ⟨Z, ι, hι, hfl, hfp, hpt⟩ := hsurj S' s ⟨x.1 ≫ U.ι, by rw [Category.assoc]; exact x.2⟩
  obtain ⟨e, hpb, hcompat⟩ := huniv S' s Z ι hι hfl hfp

  haveI : IsIso (ι ≫ prX f g s) := by
    refine (hUL (ptH S' s Z ι hι hfl hfp).1 _ e hpb (pullback.snd f s) (mX f πH (ptH S' s Z ι hι hfl hfp))
      (isPullback_mX f πH _) (ι ≫ prX f g s) ?_ ?_).mp ?_
    · rw [Category.assoc, prX_snd]
    · rw [Category.assoc, prX_comp_mX, ← Category.assoc]
      exact congrArg (fun k => k ≫ prX f g πH) hcompat
    · rw [hpt]
      rintro _ ⟨y, rfl⟩
      rw [← Scheme.Opens.range_ι U]
      exact ⟨x.1.base y, by simp [Scheme.Hom.comp_base]⟩
  obtain ⟨φ, hφ, e₀, he₀, hge⟩ := exists_graph_of_isIso f g s ι
  refine ⟨φ, hφ, ?_⟩
  apply Subtype.ext
  rw [← cancel_mono U.ι, ptM_ι]

  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S')) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have key := hnat S' S' (RingHom.id S') s s (by rw [hid, Category.id_comp])
    (pullback f s) (graph f g s φ hφ) (isClosedImmersion_graph f g s φ hφ) (flat_graph f g s φ hφ) (lfp_graph f g s φ hφ)
    Z ι hι hfl hfp e₀.hom ?_ ?_
  · rw [hid, Category.id_comp, hpt] at key
    exact key.symm
  · rw [hid]
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.comp_id, graph_snd, he₀, Category.assoc, prX_snd]
  · rw [← hge, Category.assoc]
    congr 1
    rw [← Category.comp_id (graph f g s φ hφ)]
    congr 1
    apply pullback.hom_ext
    · delta pullback.map; rw [pullback.lift_fst, Category.comp_id, Category.id_comp]
    · delta pullback.map; rw [pullback.lift_snd, hid, Category.comp_id, Category.id_comp]

theorem injM (hinj : InjH f g πH ptH)
    (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ φ' : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s) (hφ' : φ' ≫ g = pullback.snd f s ≫ s)
    (he : ptM f g πH ptH ι𝒵 U s φ hφ huniv hUL = ptM f g πH ptH ι𝒵 U s φ' hφ' huniv hUL) : φ = φ' := by
  have h1 : xH f g πH ptH s φ hφ = xH f g πH ptH s φ' hφ' := by
    apply Subtype.ext
    rw [← ptM_ι f g πH ptH ι𝒵 U s φ hφ huniv hUL, ← ptM_ι f g πH ptH ι𝒵 U s φ' hφ' huniv hUL, he]
  obtain ⟨e, he'⟩ := hinj S' s (pullback f s) (pullback f s) (graph f g s φ hφ) (graph f g s φ' hφ') _ _ _ _ _ _ h1
  exact eq_of_iso_graph f g s e he'

end Clauses
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm"

section Transport

variable {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
  (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s) (𝓛X : X.Modules) (𝓛Y : Y.Modules)

abbrev LW : (pullback f g).Modules :=
  (Scheme.Modules.pullback (pullback.fst f g)).obj 𝓛X ⊗ (Scheme.Modules.pullback (pullback.snd f g)).obj 𝓛Y

def graphIso :
    (Scheme.Modules.pullback (graph f g s φ hφ ≫ pullback.fst (fW f g) s)).obj (LW f g 𝓛X 𝓛Y) ≅
      (Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X ⊗ (Scheme.Modules.pullback φ).obj 𝓛Y :=
  Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    (((Scheme.Modules.pullbackComp _ _).app 𝓛X ≪≫ (Scheme.Modules.pullbackCongr (graph_fst_fst f g s φ hφ)).app 𝓛X) ⊗ᵢ
      ((Scheme.Modules.pullbackComp _ _).app 𝓛Y ≪≫ (Scheme.Modules.pullbackCongr (graph_fst_snd f g s φ hφ)).app 𝓛Y))

def powCongr {Z : Scheme.{0}} (M M' : Z.Modules) (η : M ≅ M') :
    ∀ d : ℕ, (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules) (fun _ N => N ⊗ M) d) ≅
      (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules) (fun _ N => N ⊗ M') d)
  | 0 => Iso.refl _
  | d + 1 => powCongr M M' η d ⊗ᵢ η

theorem locIsoOnBase_of_iso {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of S')) {M M' : Z.Modules} (η : M ≅ M') :
    AlgebraicGeometry.Polarisation.LocIsoOnBase q M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso η⟩⟩

theorem geomFibreH0Finrank_graph (k : Type) [Field k] (sk : S' →+* k) (d : ℕ) :
    Scheme.Modules.geomFibreH0Finrank (graph f g s φ hφ ≫ pullback.snd (fW f g) s)
        (Nat.rec (motive := fun _ => (pullback f s).Modules) (𝟙_ (pullback f s).Modules)
          (fun _ M => M ⊗ (Scheme.Modules.pullback (graph f g s φ hφ ≫ pullback.fst (fW f g) s)).obj (LW f g 𝓛X 𝓛Y)) d) k sk =
      Scheme.Modules.geomFibreH0Finrank (pullback.snd f s)
        (Nat.rec (motive := fun _ => (pullback f s).Modules) (𝟙_ (pullback f s).Modules)
          (fun _ M => M ⊗ ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X ⊗ (Scheme.Modules.pullback φ).obj 𝓛Y)) d) k sk := by
  rw [graph_snd]
  exact AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_locIsoOnBase (pullback.snd f s)
    (locIsoOnBase_of_iso (pullback.snd f s) (powCongr _ _ (graphIso f g s φ hφ 𝓛X 𝓛Y) d)) k sk

end Transport
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm"

end MorRepAsm
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm"

namespace MorRepAsm

variable {S : Type} [CommRing S] {X Y : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of S))

section Pieces

variable [IsSeparated g] [Flat f] [LocallyOfFinitePresentation f]
  {Hilb : Scheme.{0}} (πH : Hilb ⟶ Spec (CommRingCat.of S))
  (ptH : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (Z : Scheme.{0}) (ι : Z ⟶ pullback (fW f g) s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd (fW f g) s) →
      LocallyOfFinitePresentation (ι ≫ pullback.snd (fW f g) s) → SchemeHomOver s πH)
  {𝒵 : Scheme.{0}} (ι𝒵 : 𝒵 ⟶ pullback (fW f g) πH) (U : Hilb.Opens)
  (huniv : UnivZ f g πH ptH ι𝒵) (hUL : ULocus f g πH ι𝒵 U) (𝓛X : X.Modules) (𝓛Y : Y.Modules)

include huniv hUL

theorem piecesM [QuasiCompact U.ι]
    (hpieces : ∀ Pℚ : Polynomial ℚ, ∃ P : Hilb.Opens, IsClosed (P : Set Hilb) ∧ QuasiCompact (P.ι ≫ πH) ∧
        ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z : Scheme.{0}) (ι : Z ⟶ pullback (fW f g) s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd (fW f g) s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd (fW f g) s)),
          (Set.range (ptH S' s Z ι hι hfl hfp).1.base ⊆ (P : Set Hilb) ↔
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd (fW f g) s)
                (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst (fW f g) s)).obj (LW f g 𝓛X 𝓛Y)) d) k sk : ℕ) : ℚ) =
                Pℚ.eval (d : ℚ)))
    (Pℚ : Polynomial ℚ) :
    ∃ V : (U : Scheme.{0}).Opens, IsClosed (V : Set (U : Scheme.{0})) ∧ QuasiCompact (V.ι ≫ U.ι ≫ πH) ∧
        ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s),
          (Set.range (ptM f g πH ptH ι𝒵 U s φ hφ huniv hUL).1.base ⊆ (V : Set (U : Scheme.{0})) ↔
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (pullback.snd f s)
                (Nat.rec (motive := fun _ => (pullback f s).Modules) (𝟙_ (pullback f s).Modules)
                  (fun _ M => M ⊗ ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X ⊗ (Scheme.Modules.pullback φ).obj 𝓛Y)) d) k sk : ℕ) : ℚ) = Pℚ.eval (d : ℚ)) := by
  obtain ⟨P, hPc, hPqc, hP⟩ := hpieces Pℚ
  refine ⟨U.ι ⁻¹ᵁ P, hPc.preimage U.ι.continuous, ?_, ?_⟩
  · haveI := hPqc
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance
  · intro S' _ s φ hφ
    have hP' := hP S' s (pullback f s) (graph f g s φ hφ) (isClosedImmersion_graph f g s φ hφ) (flat_graph f g s φ hφ)
      (lfp_graph f g s φ hφ)
    simp_rw [geomFibreH0Finrank_graph] at hP'
    have hx : (ptH S' s (pullback f s) (graph f g s φ hφ) (isClosedImmersion_graph f g s φ hφ) (flat_graph f g s φ hφ)
        (lfp_graph f g s φ hφ)).1 = (ptM f g πH ptH ι𝒵 U s φ hφ huniv hUL).1 ≫ U.ι :=
      (ptM_ι f g πH ptH ι𝒵 U s φ hφ huniv hUL).symm
    rw [hx] at hP'
    rw [← hP']
    constructor
    · rintro h _ ⟨y, rfl⟩
      have hy := h ⟨y, rfl⟩
      simpa using hy
    · rintro h _ ⟨y, rfl⟩
      have hy := h ⟨y, rfl⟩
      simpa using hy

end Pieces
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm"

end MorRepAsm
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.MorRepAsm"

open MorRepAsm in
theorem solution
    (S : Type) [CommRing S] {X Y : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of S))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated g] [Flat g] [LocallyOfFinitePresentation g]
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f)
    (𝓛Y : Y.Modules) (hY₁ : Scheme.Modules.IsInvertible 𝓛Y) (hY₂ : Scheme.Modules.ClosedImmersionBySections 𝓛Y g) :
    ∃ (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of S))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (φ : pullback f s ⟶ Y), φ ≫ g = pullback.snd f s ≫ s → SchemeHomOver s πH),

      (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s),
        (pt S'' s''
            (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs])).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ).1) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πH),
        ∃ (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s), pt S' s φ hφ = x) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ φ' : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s) (hφ' : φ' ≫ g = pullback.snd f s ≫ s),
        pt S' s φ hφ = pt S' s φ' hφ' → φ = φ') ∧
      IsSeparated πH ∧ LocallyOfFinitePresentation πH ∧

      (∀ Pℚ : Polynomial ℚ, ∃ U : H.Opens, IsClosed (U : Set H) ∧ QuasiCompact (U.ι ≫ πH) ∧
        ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s),
          (Set.range (pt S' s φ hφ).1.base ⊆ (U : Set H) ↔
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (pullback.snd f s)
                (Nat.rec (motive := fun _ => (pullback f s).Modules) (𝟙_ (pullback f s).Modules)
                  (fun _ M => M ⊗ ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X ⊗ (Scheme.Modules.pullback φ).obj 𝓛Y)) d) k sk : ℕ) : ℚ) = Pℚ.eval (d : ℚ))) := by

  haveI : IsProper g := by
    obtain ⟨N, 𝔓, hci⟩ := hY₂
    rw [← 𝔓.toProj_π]
    infer_instance

  have hWci : Scheme.Modules.ClosedImmersionBySections (LW f g 𝓛X 𝓛Y) (fW f g) :=
    AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.pullback_fst_tensor_pullback_snd f g 𝓛X hX₂ 𝓛Y hY₂
  have hWinv : Scheme.Modules.IsInvertible (LW f g 𝓛X 𝓛Y) :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_monoidalV2 (hX₁.pullback _) (hY₁.pullback _)

  obtain ⟨Hilb, πH, ptH, hnat, hsurj, hinj, hsep, hlfp, hpieces⟩ :=
    AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections
      S (fW f g) (LW f g 𝓛X 𝓛Y) hWinv hWci
  obtain ⟨𝒵, ι𝒵, hZci, hZfl, hZlfp, huniv⟩ :=
    AlgebraicGeometry.exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point
      S (fW f g) πH ptH hnat hsurj hinj
  haveI := hZci
  haveI := hZfl
  haveI := hZlfp
  haveI := hsep
  haveI := hlfp

  have w : (ι𝒵 ≫ prX f g πH) ≫ pullback.snd f πH = ι𝒵 ≫ pullback.snd (fW f g) πH := by rw [Category.assoc, prX_snd]
  obtain ⟨U, hU, hUiso⟩ :=
    AlgebraicGeometry.exists_isOpen_mem_iff_isIso_fibre_and_isIso_restrict_of_isProper_of_isProper_of_flat
      (ι𝒵 ≫ pullback.snd (fW f g) πH) (pullback.snd f πH) (ι𝒵 ≫ prX f g πH) w
  obtain ⟨U', hU'qc, hU'⟩ :=
    AlgebraicGeometry.exists_isOpen_quasiCompact_inclusion_mem_iff_isIso_fibre_of_isProper_of_flat
      (ι𝒵 ≫ pullback.snd (fW f g) πH) (pullback.snd f πH) (ι𝒵 ≫ prX f g πH) w
  have hUU' : U = U' := TopologicalSpace.Opens.ext (Set.ext fun y => (hU y).trans (hU' y).symm)
  haveI : QuasiCompact U.ι := by rw [hUU']; exact hU'qc
  have hUL : ULocus f g πH ι𝒵 U := fun t pZ eZ h1 qX eX h2 φ h3 h4 =>
    AlgebraicGeometry.range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre
      (ι𝒵 ≫ pullback.snd (fW f g) πH) (pullback.snd f πH) (ι𝒵 ≫ prX f g πH) w U hU hUiso t pZ eZ h1 qX eX h2 φ h3 h4
  refine ⟨U, U.ι ≫ πH, fun S' _ s φ hφ => ptM f g πH ptH ι𝒵 U s φ hφ huniv hUL, ?_, ?_, ?_,
    inferInstance, inferInstance, ?_⟩
  · exact natM f g πH ptH ι𝒵 U huniv hUL hnat
  · exact surjM f g πH ptH ι𝒵 U huniv hUL hnat hsurj
  · intro S' _ s φ φ' hφ hφ' he
    exact injM f g πH ptH ι𝒵 U huniv hUL hinj S' s φ φ' hφ hφ' he
  · exact piecesM f g πH ptH ι𝒵 U huniv hUL 𝓛X 𝓛Y hpieces

end
end S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat (solution)
