-- Prove2me | solution 1 for AlgebraicGeometry.exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3398ab97-68d4-54d6-a68a-2fe27dc16d1d

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma
import Theorems.Thm_AlgebraicGeometry_exists_cover_forall_geomFibreH0Finrank_tensorPow_eq_eval_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.HilbertFunctor.Point.mk.injEq AlgebraicGeometry.HilbertFunctor.Point.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
p2m_open "CategoryTheory.MonoidalCategory"

noncomputable section

namespace H1PT

section BaseChange

variable {S : Type} [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S)) (𝓛X : X.Modules)

abbrev bcMap {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'') : pullback f s'' ⟶ pullback f s :=
  pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
    (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs])

theorem isPullback_bcMap {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'') :
    IsPullback (bcMap f ψ s s'' hs) (pullback.snd f s'') (pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f s) (v₁₃ := f) (h₂₂ := s) ?_ ?_ (IsPullback.of_hasPullback f s)
  · have h : bcMap f ψ s s'' hs ≫ pullback.fst f s = pullback.fst f s'' := by
      simp only [pullback.lift_fst, Category.comp_id]
    rw [h, hs]
    exact IsPullback.of_hasPullback f s''
  · simp only [pullback.lift_snd]

abbrev pow {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    {Z : Scheme.{0}} (ι : Z ⟶ pullback f s) (d : ℕ) : Z.Modules :=
  Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
    (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d

abbrev hF {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    {Z : Scheme.{0}} (ι : Z ⟶ pullback f s) (k : Type) [Field k] (sk : S' →+* k) (d : ℕ) : ℕ :=
  Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s) (pow f 𝓛X s ι d) k sk

def powIso {Y Y' : Scheme.{0}} (p : Y' ⟶ Y) (𝓜 : Y.Modules) (𝓜' : Y'.Modules)
    (η : (Scheme.Modules.pullback p).obj 𝓜 ≅ 𝓜') :
    ∀ d : ℕ, (Scheme.Modules.pullback p).obj
        (Nat.rec (motive := fun _ => Y.Modules) (𝟙_ Y.Modules) (fun _ M => M ⊗ 𝓜) d) ≅
        Nat.rec (motive := fun _ => Y'.Modules) (𝟙_ Y'.Modules) (fun _ M => M ⊗ 𝓜') d
  | 0 => Scheme.Modules.pullbackTensorUnitObjIso p
  | d + 1 => Scheme.Modules.pullbackTensorObjIso p _ 𝓜 ≪≫ (powIso p 𝓜 𝓜' η d ⊗ᵢ η)

theorem hF_baseChange {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
    {Z : Scheme.{0}} (ι : Z ⟶ pullback f s) {Z'' : Scheme.{0}} (ι'' : Z'' ⟶ pullback f s'') (e : Z'' ⟶ Z)
    (he : IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)))
    (hcomm : ι'' ≫ bcMap f ψ s s'' hs = e ≫ ι)
    (k : Type) [Field k] (sk : S'' →+* k) (d : ℕ) :
    hF f 𝓛X s'' ι'' k sk d = hF f 𝓛X s ι k (sk.comp ψ) d := by
  have hfst : bcMap f ψ s s'' hs ≫ pullback.fst f s = pullback.fst f s'' := by
    simp only [pullback.lift_fst, Category.comp_id]
  have hc : e ≫ (ι ≫ pullback.fst f s) = ι'' ≫ pullback.fst f s'' := by
    rw [← Category.assoc, ← hcomm, Category.assoc, hfst]
  let η : (Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) ≅
      (Scheme.Modules.pullback (ι'' ≫ pullback.fst f s'')).obj 𝓛X :=
    (Scheme.Modules.pullbackComp e (ι ≫ pullback.fst f s)).app 𝓛X ≪≫ eqToIso (by rw [hc])
  exact AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback ψ (ι ≫ pullback.snd f s)
    (ι'' ≫ pullback.snd f s'') e he _ _ (powIso e _ _ η d) k sk

abbrev Res {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'') {Z : Scheme.{0}} (ι : Z ⟶ pullback f s) : Scheme.{0} :=
  pullback ι (bcMap f ψ s s'' hs)

abbrev resι {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'') {Z : Scheme.{0}} (ι : Z ⟶ pullback f s) :
    Res f ψ s s'' hs ι ⟶ pullback f s'' :=
  pullback.snd ι (bcMap f ψ s s'' hs)

abbrev resE {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'') {Z : Scheme.{0}} (ι : Z ⟶ pullback f s) :
    Res f ψ s s'' hs ι ⟶ Z :=
  pullback.fst ι (bcMap f ψ s s'' hs)

theorem res_comm {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'') {Z : Scheme.{0}} (ι : Z ⟶ pullback f s) :
    resι f ψ s s'' hs ι ≫ bcMap f ψ s s'' hs = resE f ψ s s'' hs ι ≫ ι :=
  pullback.condition.symm

theorem res_isPullback {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'') {Z : Scheme.{0}} (ι : Z ⟶ pullback f s) :
    IsPullback (resE f ψ s s'' hs ι) (resι f ψ s s'' hs ι ≫ pullback.snd f s'') (ι ≫ pullback.snd f s)
      (Spec.map (CommRingCat.ofHom ψ)) :=
  (IsPullback.of_hasPullback ι (bcMap f ψ s s'' hs)).paste_vert (isPullback_bcMap f ψ s s'' hs)

theorem res_props {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'') {Z : Scheme.{0}} (ι : Z ⟶ pullback f s)
    (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
    (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) :
    IsClosedImmersion (resι f ψ s s'' hs ι) ∧ Flat (resι f ψ s s'' hs ι ≫ pullback.snd f s'') ∧
      LocallyOfFinitePresentation (resι f ψ s s'' hs ι ≫ pullback.snd f s'') := by
  refine ⟨?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (IsPullback.of_hasPullback ι (bcMap f ψ s s'' hs)) hι
  · exact MorphismProperty.of_isPullback (P := @Flat) (res_isPullback f ψ s s'' hs ι) hfl
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (res_isPullback f ψ s s'' hs ι) hfp

end BaseChange

section Pieces

variable {S : Type} [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S)) (𝓛X : X.Modules)
variable {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
  {Z : Scheme.{0}} (ι : Z ⟶ pullback f s)

structure Datum (S' : Type) [CommRing S'] where
  J : Type
  fin : Fintype J
  r : J → S'
  span_eq : Ideal.span (Set.range r) = ⊤
  Pj : J → Polynomial ℚ

def Datum.Computes (D : Datum S') : Prop :=
  ∀ (j : D.J) (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), IsUnit (sk (D.r j)) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ((hF f 𝓛X s ι k sk d : ℕ) : ℚ) = (D.Pj j).eval (d : ℚ)

def Datum.U (D : Datum S') (P : Polynomial ℚ) : (Spec (CommRingCat.of S')).Opens :=
  ⨆ j : {j : D.J // D.Pj j = P}, PrimeSpectrum.basicOpen (D.r j.1)

theorem Datum.basicOpen_le_U (D : Datum S') (j : D.J) :
    PrimeSpectrum.basicOpen (D.r j) ≤ D.U (D.Pj j) :=
  le_iSup (fun j' : {j' : D.J // D.Pj j' = D.Pj j} => PrimeSpectrum.basicOpen (R := S') (D.r j'.1)) ⟨j, rfl⟩

theorem Datum.exists_mem_basicOpen (D : Datum S') (x : Spec (CommRingCat.of S')) :
    ∃ j : D.J, x ∈ PrimeSpectrum.basicOpen (D.r j) := by
  have h : (⨆ j : D.J, PrimeSpectrum.basicOpen (D.r j)) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr D.span_eq
  have hx : x ∈ ((⨆ j : D.J, PrimeSpectrum.basicOpen (D.r j)) : TopologicalSpace.Opens _) := by rw [h]; trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

theorem Datum.iSup_U (D : Datum S') : (⨆ P, D.U P) = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨j, hj⟩ := D.exists_mem_basicOpen x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨D.Pj j, D.basicOpen_le_U j hj⟩

theorem poly_eq_of_eventually_eq {P Q : Polynomial ℚ} (d₀ : ℕ)
    (h : ∀ d : ℕ, d₀ ≤ d → P.eval (d : ℚ) = Q.eval (d : ℚ)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + d₀ : ℕ) : ℚ)) ?_ ?_
  · intro a b hab
    have hab' : ((a + d₀ : ℕ) : ℚ) = ((b + d₀ : ℕ) : ℚ) := hab
    have := Nat.cast_injective hab'
    omega
  · intro m
    exact h (m + d₀) (Nat.le_add_left d₀ m)

theorem exists_geomPoint (x : Spec (CommRingCat.of S')) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (sk : S' →+* k), RingHom.ker sk = x.asIdeal := by
  refine ⟨AlgebraicClosure x.asIdeal.ResidueField, inferInstance, inferInstance,
    (algebraMap x.asIdeal.ResidueField (AlgebraicClosure x.asIdeal.ResidueField)).comp
      (algebraMap S' x.asIdeal.ResidueField), ?_⟩
  have hinj : RingHom.ker (algebraMap x.asIdeal.ResidueField (AlgebraicClosure x.asIdeal.ResidueField)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp
      (algebraMap x.asIdeal.ResidueField (AlgebraicClosure x.asIdeal.ResidueField)).injective
  rw [← RingHom.comap_ker, hinj, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

theorem Datum.eventually_eq_of_mem_U (D : Datum S') (hD : D.Computes f 𝓛X s ι) {P : Polynomial ℚ}
    {x : Spec (CommRingCat.of S')} (hx : x ∈ D.U P)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (hk : RingHom.ker sk = x.asIdeal) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ((hF f 𝓛X s ι k sk d : ℕ) : ℚ) = P.eval (d : ℚ) := by
  rw [Datum.U] at hx
  obtain ⟨⟨j, hjP⟩, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  subst hjP
  refine hD j k sk (isUnit_iff_ne_zero.mpr fun h0 => ?_)
  have hmem : D.r j ∈ RingHom.ker sk := h0
  rw [hk] at hmem
  exact (PrimeSpectrum.mem_basicOpen _ _).mp hj hmem

theorem Datum.mem_U_of_eventually_eq (D : Datum S') (hD : D.Computes f 𝓛X s ι) {P : Polynomial ℚ}
    {x : Spec (CommRingCat.of S')}
    (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (hk : RingHom.ker sk = x.asIdeal)
    (h : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ((hF f 𝓛X s ι k sk d : ℕ) : ℚ) = P.eval (d : ℚ)) :
    x ∈ D.U P := by
  obtain ⟨j, hj⟩ := D.exists_mem_basicOpen x
  have hu : IsUnit (sk (D.r j)) := by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have hmem : D.r j ∈ RingHom.ker sk := h0
    rw [hk] at hmem
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hj hmem
  obtain ⟨d₁, h₁⟩ := hD j k sk hu
  obtain ⟨d₀, h₀⟩ := h
  have hPQ : P = D.Pj j := poly_eq_of_eventually_eq (max d₀ d₁) fun d hd => by
    rw [← h₀ d (le_of_max_le_left hd), h₁ d (le_of_max_le_right hd)]
  subst hPQ
  exact D.basicOpen_le_U j hj

theorem Datum.disjoint_U (D : Datum S') (hD : D.Computes f 𝓛X s ι) {P Q : Polynomial ℚ} (hPQ : P ≠ Q) :
    Disjoint (D.U P) (D.U Q) := by
  rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left]
  intro x hxP hxQ
  obtain ⟨k, _, _, sk, hk⟩ := exists_geomPoint x
  obtain ⟨d₀, h₀⟩ := D.eventually_eq_of_mem_U f 𝓛X s ι hD hxP k sk hk
  obtain ⟨d₁, h₁⟩ := D.eventually_eq_of_mem_U f 𝓛X s ι hD hxQ k sk hk
  exact hPQ (poly_eq_of_eventually_eq (max d₀ d₁) fun d hd => by
    rw [← h₀ d (le_of_max_le_left hd), h₁ d (le_of_max_le_right hd)])

theorem Datum.isClosed_U (D : Datum S') (hD : D.Computes f 𝓛X s ι) (P : Polynomial ℚ) :
    IsClosed ((D.U P : Set (Spec (CommRingCat.of S')))) := by
  rw [← isOpen_compl_iff]
  have hc : ((D.U P : Set (Spec (CommRingCat.of S'))))ᶜ =
      ((⨆ j : {j : D.J // D.Pj j ≠ P}, PrimeSpectrum.basicOpen (D.r j.1) :
        (Spec (CommRingCat.of S')).Opens) : Set (Spec (CommRingCat.of S'))) := by
    ext x
    rw [Set.mem_compl_iff, SetLike.mem_coe, SetLike.mem_coe]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := D.exists_mem_basicOpen x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨j, fun hjP => hx (hjP ▸ D.basicOpen_le_U j hj)⟩, hj⟩
    · intro hx' hx
      obtain ⟨⟨j, hjP⟩, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
      obtain ⟨k, _, _, sk, hk⟩ := exists_geomPoint x
      obtain ⟨d₀, h₀⟩ := D.eventually_eq_of_mem_U f 𝓛X s ι hD hx k sk hk
      obtain ⟨d₁, h₁⟩ := D.eventually_eq_of_mem_U f 𝓛X s ι hD (D.basicOpen_le_U j hj) k sk hk
      exact hjP (poly_eq_of_eventually_eq (max d₀ d₁) fun d hd => by
        rw [← h₁ d (le_of_max_le_right hd), h₀ d (le_of_max_le_left hd)])
  rw [hc]
  exact TopologicalSpace.Opens.isOpen _

theorem Datum.isAffineOpen_U (D : Datum S') (hD : D.Computes f 𝓛X s ι) (P : Polynomial ℚ) :
    IsAffineOpen (D.U P) := by
  have hclopen : IsClopen ((D.U P : Set (Spec (CommRingCat.of S')))) :=
    ⟨D.isClosed_U f 𝓛X s ι hD P, (D.U P).isOpen⟩
  obtain ⟨e, -, hUe⟩ := PrimeSpectrum.isClopen_iff.mp hclopen
  have hU : D.U P = PrimeSpectrum.basicOpen e := SetLike.coe_injective hUe
  rw [hU, ← basicOpen_eq_of_affine]
  exact (isAffineOpen_top (Spec (CommRingCat.of S'))).basicOpen _

end Pieces

section Rings

variable {S' : Type} [CommRing S']

def resHom (U : (Spec (CommRingCat.of S')).Opens) : S' →+* Γ(Spec (CommRingCat.of S'), U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ (Spec (CommRingCat.of S')).presheaf.map (homOfLE le_top).op).hom

theorem specMap_resHom (U : (Spec (CommRingCat.of S')).Opens) (hU : IsAffineOpen U) :
    Spec.map (CommRingCat.ofHom (resHom U)) = hU.fromSpec := by
  rw [resHom, CommRingCat.ofHom_hom, Spec.map_comp, ← IsAffineOpen.fromSpec_toSpecΓ hU, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

end Rings

section Main

variable {S : Type} [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S)) (𝓛X : X.Modules)
  (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f)
  (C : Polynomial ℚ → Scheme.{0}) (πC : ∀ P : Polynomial ℚ, C P ⟶ Spec (CommRingCat.of S))
  (ptC : ∀ (P : Polynomial ℚ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
        LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
        (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
          ((hF f 𝓛X s ι k sk d : ℕ) : ℚ) = P.eval (d : ℚ)) → SchemeHomOver s (πC P))

structure Sub (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) where
  Z : Scheme.{0}
  ι : Z ⟶ pullback f s
  hι : IsClosedImmersion ι
  hfl : Flat (ι ≫ pullback.snd f s)
  hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)

variable {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))

include hX₁ hX₂ in
theorem exists_datum (A : Sub f S' s) : ∃ D : Datum S', D.Computes f 𝓛X s A.ι := by
  obtain ⟨J, hJ, r, hr, Pj, h⟩ :=
    AlgebraicGeometry.exists_cover_forall_geomFibreH0Finrank_tensorPow_eq_eval_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
      S f 𝓛X hX₁ hX₂ S' s (Spec.preimage s).hom (by rw [CommRingCat.ofHom_hom, Spec.map_preimage]) A.Z A.ι A.hι A.hfl A.hfp
  exact ⟨⟨J, hJ, r, hr, Pj⟩, h⟩

def datum (A : Sub f S' s) : Datum S' := (exists_datum f 𝓛X hX₁ hX₂ s A).choose

theorem datum_computes (A : Sub f S' s) : (datum f 𝓛X hX₁ hX₂ s A).Computes f 𝓛X s A.ι :=
  (exists_datum f 𝓛X hX₁ hX₂ s A).choose_spec

def Sub.res (A : Sub f S' s) (U : (Spec (CommRingCat.of S')).Opens) :
    Sub f Γ(Spec (CommRingCat.of S'), U) (Spec.map (CommRingCat.ofHom (resHom U)) ≫ s) where
  Z := Res f (resHom U) s _ rfl A.ι
  ι := resι f (resHom U) s _ rfl A.ι
  hι := (res_props f (resHom U) s _ rfl A.ι A.hι A.hfl A.hfp).1
  hfl := (res_props f (resHom U) s _ rfl A.ι A.hι A.hfl A.hfp).2.1
  hfp := (res_props f (resHom U) s _ rfl A.ι A.hι A.hfl A.hfp).2.2

theorem res_hasHP (A : Sub f S' s) (P : Polynomial ℚ)
    (k : Type) [Field k] [IsAlgClosed k] (sk : Γ(Spec (CommRingCat.of S'), (datum f 𝓛X hX₁ hX₂ s A).U P) →+* k) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ((hF f 𝓛X (Spec.map (CommRingCat.ofHom (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P))) ≫ s)
          (A.res f s ((datum f 𝓛X hX₁ hX₂ s A).U P)).ι k sk d : ℕ) : ℚ) = P.eval (d : ℚ) := by
  have hD := datum_computes f 𝓛X hX₁ hX₂ s A
  have hU : IsAffineOpen ((datum f 𝓛X hX₁ hX₂ s A).U P) :=
    (datum f 𝓛X hX₁ hX₂ s A).isAffineOpen_U f 𝓛X s A.ι hD P

  let y : PrimeSpectrum Γ(Spec (CommRingCat.of S'), (datum f 𝓛X hX₁ hX₂ s A).U P) :=
    ⟨RingHom.ker sk, RingHom.ker_isPrime sk⟩
  have hxU : (Spec.map (CommRingCat.ofHom (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P)))).base y ∈
      (datum f 𝓛X hX₁ hX₂ s A).U P := by
    rw [specMap_resHom _ hU]
    have hy : hU.fromSpec.base y ∈ Set.range hU.fromSpec.base := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at hy
  have hk : RingHom.ker (sk.comp (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P))) =
      ((Spec.map (CommRingCat.ofHom (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P)))).base y).asIdeal := by
    change _ = (PrimeSpectrum.comap (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P)) y).asIdeal
    rw [PrimeSpectrum.comap_asIdeal]
    exact (RingHom.comap_ker sk _).symm
  obtain ⟨d₀, h⟩ := (datum f 𝓛X hX₁ hX₂ s A).eventually_eq_of_mem_U f 𝓛X s A.ι hD hxU k
    (sk.comp (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P))) hk
  refine ⟨d₀, fun d hd => ?_⟩
  have hbc := hF_baseChange f 𝓛X (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P)) s _ rfl A.ι
    (A.res f s ((datum f 𝓛X hX₁ hX₂ s A).U P)).ι (resE f (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P)) s _ rfl A.ι)
    (res_isPullback f _ s _ rfl A.ι) (res_comm f _ s _ rfl A.ι) k sk d
  rw [hbc]
  exact h d hd

def v (A : Sub f S' s) (P : Polynomial ℚ) : ((datum f 𝓛X hX₁ hX₂ s A).U P : Scheme.{0}) ⟶ C P :=
  ((datum f 𝓛X hX₁ hX₂ s A).isAffineOpen_U f 𝓛X s A.ι (datum_computes f 𝓛X hX₁ hX₂ s A) P).isoSpec.hom ≫
    (ptC P _ (Spec.map (CommRingCat.ofHom (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P))) ≫ s)
      (A.res f s _).Z (A.res f s _).ι (A.res f s _).hι (A.res f s _).hfl (A.res f s _).hfp
      (res_hasHP f 𝓛X hX₁ hX₂ s A P)).1

theorem existsUnique_ptHom (A : Sub f S' s) :
    ∃! u : Spec (CommRingCat.of S') ⟶ ∐ C,
      ∀ P, ((datum f 𝓛X hX₁ hX₂ s A).U P).ι ≫ u = v f 𝓛X hX₁ hX₂ C πC ptC s A P ≫ Sigma.ι C P :=
  AlgebraicGeometry.Scheme.existsUnique_hom_sigma_of_disjoint_iSup_eq_top C (fun P => (datum f 𝓛X hX₁ hX₂ s A).U P)
    (fun P Q h => (datum f 𝓛X hX₁ hX₂ s A).disjoint_U f 𝓛X s A.ι (datum_computes f 𝓛X hX₁ hX₂ s A) h)
    ((datum f 𝓛X hX₁ hX₂ s A).iSup_U) (v f 𝓛X hX₁ hX₂ C πC ptC s A)

def ptHom (A : Sub f S' s) : Spec (CommRingCat.of S') ⟶ ∐ C :=
  (existsUnique_ptHom f 𝓛X hX₁ hX₂ C πC ptC s A).exists.choose

theorem ptHom_spec (A : Sub f S' s) (P : Polynomial ℚ) :
    ((datum f 𝓛X hX₁ hX₂ s A).U P).ι ≫ ptHom f 𝓛X hX₁ hX₂ C πC ptC s A =
      v f 𝓛X hX₁ hX₂ C πC ptC s A P ≫ Sigma.ι C P :=
  (existsUnique_ptHom f 𝓛X hX₁ hX₂ C πC ptC s A).exists.choose_spec P

theorem ptHom_unique (A : Sub f S' s) (u : Spec (CommRingCat.of S') ⟶ ∐ C)
    (hu : ∀ P, ((datum f 𝓛X hX₁ hX₂ s A).U P).ι ≫ u = v f 𝓛X hX₁ hX₂ C πC ptC s A P ≫ Sigma.ι C P) :
    u = ptHom f 𝓛X hX₁ hX₂ C πC ptC s A :=
  (existsUnique_ptHom f 𝓛X hX₁ hX₂ C πC ptC s A).unique hu
    (existsUnique_ptHom f 𝓛X hX₁ hX₂ C πC ptC s A).exists.choose_spec

theorem ptHom_over (A : Sub f S' s) : ptHom f 𝓛X hX₁ hX₂ C πC ptC s A ≫ Sigma.desc πC = s := by
  apply Scheme.hom_ext_of_forall
  intro x
  have hx : x ∈ ((⨆ P, (datum f 𝓛X hX₁ hX₂ s A).U P : (Spec (CommRingCat.of S')).Opens)) := by
    rw [(datum f 𝓛X hX₁ hX₂ s A).iSup_U]; trivial
  obtain ⟨P, hP⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨(datum f 𝓛X hX₁ hX₂ s A).U P, hP, ?_⟩
  have hU : IsAffineOpen ((datum f 𝓛X hX₁ hX₂ s A).U P) :=
    (datum f 𝓛X hX₁ hX₂ s A).isAffineOpen_U f 𝓛X s A.ι (datum_computes f 𝓛X hX₁ hX₂ s A) P
  have h2 := (ptC P _ _ (A.res f s ((datum f 𝓛X hX₁ hX₂ s A).U P)).Z (A.res f s _).ι (A.res f s _).hι
    (A.res f s _).hfl (A.res f s _).hfp (res_hasHP f 𝓛X hX₁ hX₂ s A P)).2
  rw [← Category.assoc, ptHom_spec, Category.assoc, Sigma.ι_desc]
  dsimp only [v]
  rw [Category.assoc, h2, specMap_resHom _ hU, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc,
    Iso.hom_inv_id_assoc]

def pt (A : Sub f S' s) : SchemeHomOver s (Sigma.desc πC) :=
  ⟨ptHom f 𝓛X hX₁ hX₂ C πC ptC s A, ptHom_over f 𝓛X hX₁ hX₂ C πC ptC s A⟩

end Main

section Clauses

variable {S : Type} [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S)) (𝓛X : X.Modules)
  (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f)
  (C : Polynomial ℚ → Scheme.{0}) (πC : ∀ P : Polynomial ℚ, C P ⟶ Spec (CommRingCat.of S))
  (ptC : ∀ (P : Polynomial ℚ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
        LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
        (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
          ((hF f 𝓛X s ι k sk d : ℕ) : ℚ) = P.eval (d : ℚ)) → SchemeHomOver s (πC P))
  (hnatC : ∀ (P : Polynomial ℚ),
      (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((hF f 𝓛X s ι k sk d : ℕ) : ℚ) = P.eval (d : ℚ)))
          (Z'' : Scheme.{0}) (ι'' : Z'' ⟶ pullback f s'') (hι'' : IsClosedImmersion ι'') (hfl'' : Flat (ι'' ≫ pullback.snd f s''))
          (hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd f s''))
          (hHP'' : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S'' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((hF f 𝓛X s'' ι'' k sk d : ℕ) : ℚ) = P.eval (d : ℚ)))
          (e : Z'' ⟶ Z),
          IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) →
          ι'' ≫ bcMap f ψ s s'' hs = e ≫ ι →
          (ptC P S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptC P S' s Z ι hι hfl hfp hHP).1))

theorem isoSpec_hom_specMap_appLE {T T'' : Scheme.{0}} (g : T'' ⟶ T) {U : T.Opens} {U'' : T''.Opens}
    (hU : IsAffineOpen U) (hU'' : IsAffineOpen U'') (hle : U'' ≤ g ⁻¹ᵁ U) :
    hU''.isoSpec.hom ≫ Spec.map (g.appLE U U'' hle) = g.resLE U U'' hle ≫ hU.isoSpec.hom := by
  rw [← cancel_mono hU.isoSpec.inv, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← cancel_mono U.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    IsAffineOpen.SpecMap_appLE_fromSpec g hU hU'' hle, Scheme.Hom.resLE_comp_ι,
    ← IsAffineOpen.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc]

variable {S' S'' : Type} [CommRing S'] [CommRing S'']

theorem U_baseChange (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'') (A : Sub f S' s) (A'' : Sub f S'' s'') (e : A''.Z ⟶ A.Z)
    (he : IsPullback e (A''.ι ≫ pullback.snd f s'') (A.ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)))
    (hcomm : A''.ι ≫ bcMap f ψ s s'' hs = e ≫ A.ι) (P : Polynomial ℚ) :
    (datum f 𝓛X hX₁ hX₂ s'' A'').U P = Spec.map (CommRingCat.ofHom ψ) ⁻¹ᵁ (datum f 𝓛X hX₁ hX₂ s A).U P := by
  have hD := datum_computes f 𝓛X hX₁ hX₂ s A
  have hD'' := datum_computes f 𝓛X hX₁ hX₂ s'' A''
  have key : ∀ x'' : Spec (CommRingCat.of S''),
      x'' ∈ (datum f 𝓛X hX₁ hX₂ s'' A'').U P ↔
        (Spec.map (CommRingCat.ofHom ψ)).base x'' ∈ (datum f 𝓛X hX₁ hX₂ s A).U P := by
    intro x''
    obtain ⟨k, _, _, sk, hk⟩ := exists_geomPoint x''
    have hk' : RingHom.ker (sk.comp ψ) = ((Spec.map (CommRingCat.ofHom ψ)).base x'').asIdeal := by
      change _ = (PrimeSpectrum.comap ψ x'').asIdeal
      rw [PrimeSpectrum.comap_asIdeal, ← hk]
      exact (RingHom.comap_ker sk ψ).symm
    have hbc : ∀ d : ℕ, hF f 𝓛X s'' A''.ι k sk d = hF f 𝓛X s A.ι k (sk.comp ψ) d := fun d =>
      hF_baseChange f 𝓛X ψ s s'' hs A.ι A''.ι e he hcomm k sk d
    constructor
    · intro hx
      obtain ⟨d₀, h₀⟩ := (datum f 𝓛X hX₁ hX₂ s'' A'').eventually_eq_of_mem_U f 𝓛X s'' A''.ι hD'' hx k sk hk
      exact (datum f 𝓛X hX₁ hX₂ s A).mem_U_of_eventually_eq f 𝓛X s A.ι hD k (sk.comp ψ) hk'
        ⟨d₀, fun d hd => by rw [← hbc d]; exact h₀ d hd⟩
    · intro hx
      obtain ⟨d₀, h₀⟩ := (datum f 𝓛X hX₁ hX₂ s A).eventually_eq_of_mem_U f 𝓛X s A.ι hD hx k (sk.comp ψ) hk'
      exact (datum f 𝓛X hX₁ hX₂ s'' A'').mem_U_of_eventually_eq f 𝓛X s'' A''.ι hD'' k sk hk
        ⟨d₀, fun d hd => by rw [hbc d]; exact h₀ d hd⟩
  exact TopologicalSpace.Opens.ext (Set.ext key)

include hnatC in

theorem pt_const (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (P : Polynomial ℚ) (A : Sub f S' s)
    (hHP : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ((hF f 𝓛X s A.ι k sk d : ℕ) : ℚ) = P.eval (d : ℚ)) :
    (pt f 𝓛X hX₁ hX₂ C πC ptC s A).1 = (ptC P S' s A.Z A.ι A.hι A.hfl A.hfp hHP).1 ≫ Sigma.ι C P := by
  classical
  have hDc := datum_computes f 𝓛X hX₁ hX₂ s A
  have hUa := (datum f 𝓛X hX₁ hX₂ s A).isAffineOpen_U f 𝓛X s A.ι hDc P

  have hU : (datum f 𝓛X hX₁ hX₂ s A).U P = ⊤ := top_le_iff.mp fun x _ => by
    obtain ⟨k, _, _, sk, hk⟩ := exists_geomPoint x
    exact (datum f 𝓛X hX₁ hX₂ s A).mem_U_of_eventually_eq f 𝓛X s A.ι hDc k sk hk (hHP k sk)
  have hiso : IsIso ((⊤ : (Spec (CommRingCat.of S')).Opens).ι) :=
    ⟨⟨(Spec (CommRingCat.of S')).topIso.inv, Scheme.ι_toIso_inv _, Scheme.toIso_inv_ι _⟩⟩
  haveI : IsIso ((datum f 𝓛X hX₁ hX₂ s A).U P).ι := by
    rw [← Scheme.isoOfEq_hom_ι _ hU]; infer_instance
  rw [← cancel_epi ((datum f 𝓛X hX₁ hX₂ s A).U P).ι]
  change ((datum f 𝓛X hX₁ hX₂ s A).U P).ι ≫ ptHom f 𝓛X hX₁ hX₂ C πC ptC s A = _
  rw [ptHom_spec]
  have key := hnatC P S' _ (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P)) s _ rfl A.Z A.ι A.hι A.hfl A.hfp hHP
    (A.res f s ((datum f 𝓛X hX₁ hX₂ s A).U P)).Z (A.res f s ((datum f 𝓛X hX₁ hX₂ s A).U P)).ι
    (A.res f s _).hι (A.res f s _).hfl (A.res f s _).hfp (res_hasHP f 𝓛X hX₁ hX₂ s A P)
    (resE f (resHom _) s _ rfl A.ι) (res_isPullback f (resHom _) s _ rfl A.ι) (res_comm f (resHom _) s _ rfl A.ι)
  simp only [v, Category.assoc]
  rw [key, specMap_resHom _ hUa, ← IsAffineOpen.isoSpec_inv_ι]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

include hnatC in

theorem pt_nat (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'') (A : Sub f S' s) (A'' : Sub f S'' s'') (e : A''.Z ⟶ A.Z)
    (he : IsPullback e (A''.ι ≫ pullback.snd f s'') (A.ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)))
    (hcomm : A''.ι ≫ bcMap f ψ s s'' hs = e ≫ A.ι) :
    (pt f 𝓛X hX₁ hX₂ C πC ptC s'' A'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt f 𝓛X hX₁ hX₂ C πC ptC s A).1 := by
  classical
  have hDc := datum_computes f 𝓛X hX₁ hX₂ s A
  have hDc'' := datum_computes f 𝓛X hX₁ hX₂ s'' A''
  change ptHom f 𝓛X hX₁ hX₂ C πC ptC s'' A'' = Spec.map (CommRingCat.ofHom ψ) ≫ ptHom f 𝓛X hX₁ hX₂ C πC ptC s A
  symm
  apply ptHom_unique
  intro P
  have hUeq := U_baseChange f 𝓛X hX₁ hX₂ ψ s s'' hs A A'' e he hcomm P
  have hle : (datum f 𝓛X hX₁ hX₂ s'' A'').U P ≤
      Spec.map (CommRingCat.ofHom ψ) ⁻¹ᵁ (datum f 𝓛X hX₁ hX₂ s A).U P := hUeq.le
  have hUa := (datum f 𝓛X hX₁ hX₂ s A).isAffineOpen_U f 𝓛X s A.ι hDc P
  have hUa'' := (datum f 𝓛X hX₁ hX₂ s'' A'').isAffineOpen_U f 𝓛X s'' A''.ι hDc'' P

  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (Spec.map (CommRingCat.ofHom ψ)).appLE ((datum f 𝓛X hX₁ hX₂ s A).U P)
    ((datum f 𝓛X hX₁ hX₂ s'' A'').U P) hle := ⟨_, rfl⟩
  have hsq : Spec.map (CommRingCat.ofHom φ.hom) ≫
      Spec.map (CommRingCat.ofHom (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P))) =
      Spec.map (CommRingCat.ofHom (resHom ((datum f 𝓛X hX₁ hX₂ s'' A'').U P))) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    rw [CommRingCat.ofHom_hom, specMap_resHom _ hUa, specMap_resHom _ hUa'', hφ, IsAffineOpen.SpecMap_appLE_fromSpec]
  have hsPP : Spec.map (CommRingCat.ofHom φ.hom) ≫
      (Spec.map (CommRingCat.ofHom (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P))) ≫ s) =
      Spec.map (CommRingCat.ofHom (resHom ((datum f 𝓛X hX₁ hX₂ s'' A'').U P))) ≫ s'' := by
    rw [← Category.assoc, hsq, Category.assoc, hs]

  have hbc : bcMap f (resHom ((datum f 𝓛X hX₁ hX₂ s'' A'').U P)) s'' _ rfl ≫ bcMap f ψ s s'' hs =
      bcMap f φ.hom _ _ hsPP ≫ bcMap f (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P)) s _ rfl := by
    apply pullback.hom_ext
    · simp only [bcMap, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [bcMap, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [hsq]

  let ePP : (A''.res f s'' ((datum f 𝓛X hX₁ hX₂ s'' A'').U P)).Z ⟶ (A.res f s ((datum f 𝓛X hX₁ hX₂ s A).U P)).Z :=
    pullback.lift (resE f (resHom _) s'' _ rfl A''.ι ≫ e)
      (resι f (resHom _) s'' _ rfl A''.ι ≫ bcMap f φ.hom _ _ hsPP) (by
        have rc := res_comm f (resHom ((datum f 𝓛X hX₁ hX₂ s'' A'').U P)) s'' _ rfl A''.ι
        have h1 := congrArg (· ≫ bcMap f ψ s s'' hs) rc.symm
        simp only [Category.assoc, ← hcomm, ← hbc]
        simp only [Category.assoc] at h1
        exact h1)
  have hePP_fst : ePP ≫ resE f (resHom _) s _ rfl A.ι = resE f (resHom _) s'' _ rfl A''.ι ≫ e :=
    pullback.lift_fst _ _ _
  have hePP_snd : ePP ≫ resι f (resHom _) s _ rfl A.ι = resι f (resHom _) s'' _ rfl A''.ι ≫ bcMap f φ.hom _ _ hsPP :=
    pullback.lift_snd _ _ _
  have hcommPP : (A''.res f s'' ((datum f 𝓛X hX₁ hX₂ s'' A'').U P)).ι ≫ bcMap f φ.hom _ _ hsPP =
      ePP ≫ (A.res f s ((datum f 𝓛X hX₁ hX₂ s A).U P)).ι := hePP_snd.symm
  have hePP : IsPullback ePP ((A''.res f s'' ((datum f 𝓛X hX₁ hX₂ s'' A'').U P)).ι ≫ pullback.snd f _)
      ((A.res f s ((datum f 𝓛X hX₁ hX₂ s A).U P)).ι ≫ pullback.snd f _) (Spec.map (CommRingCat.ofHom φ.hom)) := by
    have big := (res_isPullback f (resHom ((datum f 𝓛X hX₁ hX₂ s'' A'').U P)) s'' _ rfl A''.ι).paste_horiz he
    rw [← hePP_fst, ← hsq] at big
    refine big.of_right ?_ (res_isPullback f (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P)) s _ rfl A.ι)
    have h2 : bcMap f φ.hom _ _ hsPP ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P))) ≫ s) =
        pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom φ.hom) := pullback.lift_snd _ _ _
    have h3 := congrArg (· ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (resHom ((datum f 𝓛X hX₁ hX₂ s A).U P))) ≫ s)) hePP_snd
    refine ((Category.assoc _ _ _).symm.trans h3).trans ?_
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    exact congrArg (resι f (resHom ((datum f 𝓛X hX₁ hX₂ s'' A'').U P)) s'' _ rfl A''.ι ≫ ·) h2
  have key := hnatC P _ _ φ.hom _ _ hsPP
    (A.res f s ((datum f 𝓛X hX₁ hX₂ s A).U P)).Z (A.res f s _).ι (A.res f s _).hι (A.res f s _).hfl (A.res f s _).hfp
    (res_hasHP f 𝓛X hX₁ hX₂ s A P)
    (A''.res f s'' ((datum f 𝓛X hX₁ hX₂ s'' A'').U P)).Z (A''.res f s'' _).ι (A''.res f s'' _).hι (A''.res f s'' _).hfl
    (A''.res f s'' _).hfp (res_hasHP f 𝓛X hX₁ hX₂ s'' A'' P) ePP hePP hcommPP

  rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι _ hle, Category.assoc, ptHom_spec, ← Category.assoc]
  congr 1
  simp only [v]
  rw [key, ← Category.assoc, ← Category.assoc, CommRingCat.ofHom_hom, hφ,
    isoSpec_hom_specMap_appLE (Spec.map (CommRingCat.ofHom ψ)) hUa hUa'' hle]

end Clauses

end H1PT

end

theorem solution
    (S : Type) [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S))
    [Flat f] [LocallyOfFinitePresentation f]
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f)
    (C : Polynomial ℚ → Scheme.{0}) (πC : ∀ P : Polynomial ℚ, C P ⟶ Spec (CommRingCat.of S))
    (ptC : ∀ (P : Polynomial ℚ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
          (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) →
          SchemeHomOver s (πC P))
    (hnatC : ∀ (P : Polynomial ℚ),
        (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
            (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
            (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
            (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
            (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
            (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
                (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                P.eval (d : ℚ)))
            (Z'' : Scheme.{0}) (ι'' : Z'' ⟶ pullback f s'') (hι'' : IsClosedImmersion ι'') (hfl'' : Flat (ι'' ≫ pullback.snd f s''))
            (hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd f s''))
            (hHP'' : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S'' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι'' ≫ pullback.snd f s'')
                (Nat.rec (motive := fun _ => Z''.Modules) (𝟙_ Z''.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι'' ≫ pullback.fst f s'')).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                P.eval (d : ℚ)))
            (e : Z'' ⟶ Z),
            IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) →
            ι'' ≫ pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
                (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs]) = e ≫ ι →
            (ptC P S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptC P S' s Z ι hι hfl hfp hHP).1)) :
    ∃ (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) → SchemeHomOver s (Sigma.desc πC)),

      (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (Z'' : Scheme.{0}) (ι'' : Z'' ⟶ pullback f s'') (hι'' : IsClosedImmersion ι'') (hfl'' : Flat (ι'' ≫ pullback.snd f s''))
          (hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd f s''))
          (e : Z'' ⟶ Z),

          IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) →
          ι'' ≫ pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
              (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs]) = e ≫ ι →
          (pt S'' s'' Z'' ι'' hι'' hfl'' hfp'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s Z ι hι hfl hfp).1) ∧

      (∀ (P : Polynomial ℚ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ))),
        (pt S' s Z ι hι hfl hfp).1 = (ptC P S' s Z ι hι hfl hfp hHP).1 ≫ Sigma.ι C P) := by
  classical
  refine ⟨fun S' _ s Z ι hι hfl hfp => H1PT.pt f 𝓛X hX₁ hX₂ C πC ptC s ⟨Z, ι, hι, hfl, hfp⟩, ?_, ?_⟩
  · intro S' S'' _ _ ψ s s'' hs Z ι hι hfl hfp Z'' ι'' hι'' hfl'' hfp'' e he hcomm
    exact H1PT.pt_nat f 𝓛X hX₁ hX₂ C πC ptC hnatC ψ s s'' hs ⟨Z, ι, hι, hfl, hfp⟩ ⟨Z'', ι'', hι'', hfl'', hfp''⟩ e he hcomm
  · intro P S' _ s Z ι hι hfl hfp hHP
    exact H1PT.pt_const f 𝓛X hX₁ hX₂ C πC ptC hnatC s P ⟨Z, ι, hι, hfl, hfp⟩ hHP

end S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq
end P2MW
export P2MW.S_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq (solution)
