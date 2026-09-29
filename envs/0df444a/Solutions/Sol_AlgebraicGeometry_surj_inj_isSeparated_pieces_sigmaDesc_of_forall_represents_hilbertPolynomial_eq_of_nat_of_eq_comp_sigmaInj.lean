-- Prove2me | solution 1 for AlgebraicGeometry.surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d76e320b-a404-577f-936a-28c3335bfd63

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_exists_cover_forall_geomFibreH0Finrank_tensorPow_eq_eval_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap
import Theorems.Thm_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.HilbertFunctor.Point.mk.injEq AlgebraicGeometry.HilbertFunctor.Point.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
p2m_open "CategoryTheory.MonoidalCategory"

noncomputable section

namespace H1SIC

variable {S : Type} [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S)) (𝓛X : X.Modules)

section Pow

variable {S' : Type} [CommRing S'] {s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)} {Z : Scheme.{0}}

abbrev Lpow (ι : Z ⟶ pullback f s) (d : ℕ) : Z.Modules :=
  Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
    (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d

abbrev hval (ι : Z ⟶ pullback f s) (k : Type) [Field k] (sk : S' →+* k) (d : ℕ) : ℕ :=
  Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s) (Lpow f 𝓛X ι d) k sk

def HP (ι : Z ⟶ pullback f s) (P : Polynomial ℚ) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
      (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
        (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
      P.eval (d : ℚ)

theorem HP_iff (ι : Z ⟶ pullback f s) (P : Polynomial ℚ) :
    HP f 𝓛X ι P ↔ ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ((hval f 𝓛X ι k sk d : ℕ) : ℚ) = P.eval (d : ℚ) := Iff.rfl

theorem poly_eq_of_eventually {P Q : Polynomial ℚ} {h : ℕ → ℕ}
    (hP : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ((h d : ℕ) : ℚ) = P.eval (d : ℚ))
    (hQ : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ((h d : ℕ) : ℚ) = Q.eval (d : ℚ)) : P = Q := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  apply Polynomial.eq_of_infinite_eval_eq
  have hsub : Set.range (fun n : ℕ => ((max a b + n : ℕ) : ℚ)) ⊆ {x | Polynomial.eval x P = Polynomial.eval x Q} := by
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [← ha _ (by omega), ← hb _ (by omega)]
  refine Set.Infinite.mono hsub (Set.infinite_range_of_injective ?_)
  intro m n hmn
  have := (Nat.cast_injective (R := ℚ)) hmn
  omega

end Pow

section BC

variable {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
  (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
  (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')

abbrev jmap : pullback f s'' ⟶ pullback f s :=
  pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
    (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs])

@[reassoc (attr := simp)]
theorem jmap_fst : jmap f ψ s s'' hs ≫ pullback.fst f s = pullback.fst f s'' := by
  delta jmap pullback.map
  rw [pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem jmap_snd : jmap f ψ s s'' hs ≫ pullback.snd f s = pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ) := by
  delta jmap pullback.map
  rw [pullback.lift_snd]

include hs in
theorem isPullback_jmap :
    IsPullback (jmap f ψ s s'' hs) (pullback.snd f s'') (pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f s) (v₁₃ := f) (h₂₂ := s) ?_ (jmap_snd f ψ s s'' hs)
    (IsPullback.of_hasPullback f s)
  rw [jmap_fst, hs]
  exact IsPullback.of_hasPullback f s''

scoped instance isOpenImmersion_jmap [IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ))] :
    IsOpenImmersion (jmap f ψ s s'' hs) :=
  MorphismProperty.of_isPullback (isPullback_jmap f ψ s s'' hs).flip inferInstance

omit hs in

theorem range_eq_of_isPullback {P₀ X₀ Y₀ T₀ : Scheme.{0}} {a : P₀ ⟶ X₀} {b : P₀ ⟶ Y₀} {u : X₀ ⟶ T₀} {v : Y₀ ⟶ T₀}
    (h : IsPullback a b u v) : Set.range a = u ⁻¹' Set.range v := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr h.isoPullback.hom.surjective, Set.image_univ, Scheme.Pullback.range_fst]

theorem opensRange_jmap [IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ))] :
    (jmap f ψ s s'' hs).opensRange = pullback.snd f s ⁻¹ᵁ (Spec.map (CommRingCat.ofHom ψ)).opensRange := by
  apply TopologicalSpace.Opens.ext
  simpa using range_eq_of_isPullback (isPullback_jmap f ψ s s'' hs)

variable {Z Z'' : Scheme.{0}} (ι : Z ⟶ pullback f s) (ι'' : Z'' ⟶ pullback f s'') (e : Z'' ⟶ Z)

def powIsoOfComm (hcomm : ι'' ≫ jmap f ψ s s'' hs = e ≫ ι) :
    ∀ d : ℕ, (Scheme.Modules.pullback e).obj (Lpow f 𝓛X ι d) ≅ Lpow f 𝓛X ι'' d
  | 0 => Scheme.Modules.pullbackTensorUnitObjIso e
  | d + 1 => Scheme.Modules.pullbackTensorObjIso e _ _ ≪≫
      (powIsoOfComm hcomm d ⊗ᵢ
        ((Scheme.Modules.pullbackComp e (ι ≫ pullback.fst f s)).app 𝓛X ≪≫
          (Scheme.Modules.pullbackCongr (show e ≫ ι ≫ pullback.fst f s = ι'' ≫ pullback.fst f s'' by
            rw [← Category.assoc, ← hcomm, Category.assoc, jmap_fst])).app 𝓛X))

theorem hval_eq_of_isPullback
    (hpb : IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)))
    (hcomm : ι'' ≫ jmap f ψ s s'' hs = e ≫ ι) (k : Type) [Field k] (sk : S'' →+* k) (d : ℕ) :
    hval f 𝓛X ι'' k sk d = hval f 𝓛X ι k (sk.comp ψ) d :=
  AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback ψ (ι ≫ pullback.snd f s)
    (ι'' ≫ pullback.snd f s'') e hpb (Lpow f 𝓛X ι d) (Lpow f 𝓛X ι'' d) (powIsoOfComm f 𝓛X ψ s s'' hs ι ι'' e hcomm d) k sk

theorem HP_of_isPullback
    (hpb : IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)))
    (hcomm : ι'' ≫ jmap f ψ s s'' hs = e ≫ ι) {P : Polynomial ℚ} (h : HP f 𝓛X ι P) : HP f 𝓛X ι'' P := by
  rw [HP_iff] at h ⊢
  intro k _ _ sk
  obtain ⟨d₀, hd⟩ := h k (sk.comp ψ)
  exact ⟨d₀, fun d hdd => by rw [hval_eq_of_isPullback f 𝓛X ψ s s'' hs ι ι'' e hpb hcomm]; exact hd d hdd⟩

abbrev bcObj : Scheme.{0} := pullback ι (jmap f ψ s s'' hs)

abbrev bcι : bcObj f ψ s s'' hs ι ⟶ pullback f s'' := pullback.snd ι (jmap f ψ s s'' hs)

abbrev bcE : bcObj f ψ s s'' hs ι ⟶ Z := pullback.fst ι (jmap f ψ s s'' hs)

theorem bc_comm : bcι f ψ s s'' hs ι ≫ jmap f ψ s s'' hs = bcE f ψ s s'' hs ι ≫ ι :=
  pullback.condition.symm

theorem isPullback_bc :
    IsPullback (bcE f ψ s s'' hs ι) (bcι f ψ s s'' hs ι ≫ pullback.snd f s'') (ι ≫ pullback.snd f s)
      (Spec.map (CommRingCat.ofHom ψ)) :=
  (IsPullback.of_hasPullback ι (jmap f ψ s s'' hs)).paste_vert (isPullback_jmap f ψ s s'' hs)

scoped instance bcι_isClosedImmersion [IsClosedImmersion ι] : IsClosedImmersion (bcι f ψ s s'' hs ι) := inferInstance

theorem bc_flat [Flat (ι ≫ pullback.snd f s)] : Flat (bcι f ψ s s'' hs ι ≫ pullback.snd f s'') :=
  MorphismProperty.of_isPullback (isPullback_bc f ψ s s'' hs ι) inferInstance

theorem bc_lfp [LocallyOfFinitePresentation (ι ≫ pullback.snd f s)] :
    LocallyOfFinitePresentation (bcι f ψ s s'' hs ι ≫ pullback.snd f s'') :=
  MorphismProperty.of_isPullback (isPullback_bc f ψ s s'' hs ι) inferInstance

theorem bc_HP {P : Polynomial ℚ} (h : HP f 𝓛X ι P) : HP f 𝓛X (bcι f ψ s s'' hs ι) P :=
  HP_of_isPullback f 𝓛X ψ s s'' hs ι _ _ (isPullback_bc f ψ s s'' hs ι) (bc_comm f ψ s s'' hs ι) h

scoped instance bcE_isOpenImmersion [IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ))] :
    IsOpenImmersion (bcE f ψ s s'' hs ι) :=
  MorphismProperty.of_isPullback (isPullback_bc f ψ s s'' hs ι).flip inferInstance

theorem opensRange_bcE [IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ))] :
    (bcE f ψ s s'' hs ι).opensRange = (ι ≫ pullback.snd f s) ⁻¹ᵁ (Spec.map (CommRingCat.ofHom ψ)).opensRange := by
  apply TopologicalSpace.Opens.ext
  have h__af := range_eq_of_isPullback (isPullback_bc f ψ s s'' hs ι)
  simp [Set.preimage_preimage] at h__af
  exact h__af

end BC

end H1SIC
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC"

noncomputable section

namespace H1SIC

variable {S : Type} [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S)) (𝓛X : X.Modules)

structure Fam where

  C : Polynomial ℚ → Scheme.{0}

  πC : ∀ P : Polynomial ℚ, C P ⟶ Spec (CommRingCat.of S)

  ptC : ∀ (P : Polynomial ℚ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
          (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) →
          SchemeHomOver s (πC P)
  natC : ∀ (P : Polynomial ℚ),
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
          (ptC P S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptC P S' s Z ι hι hfl hfp hHP).1)
  surjC : ∀ (P : Polynomial ℚ),
      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s (πC P)),
        ∃ (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ))),
          ptC P S' s Z ι hι hfl hfp hHP = x)
  injC : ∀ (P : Polynomial ℚ),
      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z Z' : Scheme.{0}) (ι : Z ⟶ pullback f s) (ι' : Z' ⟶ pullback f s)
          (hι : IsClosedImmersion ι) (hι' : IsClosedImmersion ι')
          (hfl : Flat (ι ≫ pullback.snd f s)) (hfl' : Flat (ι' ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f s))
          (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)))
          (hHP' : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι' ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z'.Modules) (𝟙_ Z'.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι' ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ))),
        ptC P S' s Z ι hι hfl hfp hHP = ptC P S' s Z' ι' hι' hfl' hfp' hHP' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι)
  properC : ∀ P : Polynomial ℚ, IsProper (πC P)
  lfpC : ∀ P : Polynomial ℚ, LocallyOfFinitePresentation (πC P)

  pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) → SchemeHomOver s (Sigma.desc πC)
  nat :
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
          (pt S'' s'' Z'' ι'' hι'' hfl'' hfp'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s Z ι hι hfl hfp).1)
  const :
      (∀ (P : Polynomial ℚ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ))),
        (pt S' s Z ι hι hfl hfp).1 = (ptC P S' s Z ι hι hfl hfp hHP).1 ≫ Sigma.ι C P)

namespace Fam

variable {f} {𝓛X} (F : Fam f 𝓛X)

theorem eq_of_mem_opensRange {P Q : Polynomial ℚ} {y : ↥(∐ F.C)}
    (hP : y ∈ (Sigma.ι F.C P).opensRange) (hQ : y ∈ (Sigma.ι F.C Q).opensRange) : P = Q := by
  by_contra h
  have hd := disjoint_opensRange_sigmaι F.C P Q h
  rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left] at hd
  exact hd hP hQ

section Loc

variable (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f)

include hX₁ hX₂ in

theorem eventually_eq_of_range_subset
    {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
    (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
    (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (P : Polynomial ℚ)
    (hmem : Set.range ⇑(Spec.map (CommRingCat.ofHom sk) ≫ (F.pt S' s Z ι hι hfl hfp).1) ⊆
      ((Sigma.ι F.C P).opensRange : Set ↥(∐ F.C))) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ((hval f 𝓛X ι k sk d : ℕ) : ℚ) = P.eval (d : ℚ) := by
  obtain ⟨J, _, r, hspan, Pj, hloc⟩ :=
    AlgebraicGeometry.exists_cover_forall_geomFibreH0Finrank_tensorPow_eq_eval_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation S f 𝓛X hX₁ hX₂ S' s
      (Spec.preimage s).hom (by rw [CommRingCat.ofHom_hom, Spec.map_preimage]) Z ι hι hfl hfp

  have hj : ∃ j, IsUnit (sk (r j)) := by
    by_contra hall
    push Not at hall
    have hle : Ideal.span (Set.range r) ≤ RingHom.ker sk := Ideal.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      simpa [RingHom.mem_ker, isUnit_iff_ne_zero] using hall j)
    rw [hspan, top_le_iff] at hle
    exact RingHom.ker_ne_top sk hle
  obtain ⟨j, hj⟩ := hj
  obtain ⟨d₁, hd₁⟩ := hloc j k sk hj
  suffices hPP : P = Pj j by subst hPP; exact ⟨d₁, hd₁⟩

  let A : Type := Localization.Away (r j)
  let ψ : S' →+* A := algebraMap S' A
  haveI := hι; haveI := hfl; haveI := hfp
  have hHPj : HP f 𝓛X (bcι f ψ s _ rfl ι) (Pj j) := by
    rw [HP_iff]
    intro k' _ _ sk'
    obtain ⟨d₂, hd₂⟩ := hloc j k' (sk'.comp ψ) (by
      simpa using (IsLocalization.Away.algebraMap_isUnit (S := A) (r j)).map sk')
    exact ⟨d₂, fun d hd => by rw [hval_eq_of_isPullback f 𝓛X ψ s _ rfl ι _ _ (isPullback_bc f ψ s _ rfl ι)
      (bc_comm f ψ s _ rfl ι)]; exact hd₂ d hd⟩
  have hc := F.const (Pj j) A (Spec.map (CommRingCat.ofHom ψ) ≫ s) _ (bcι f ψ s _ rfl ι) inferInstance
    (bc_flat f ψ s _ rfl ι) (bc_lfp f ψ s _ rfl ι) hHPj
  have hn := F.nat S' A ψ s (Spec.map (CommRingCat.ofHom ψ) ≫ s) rfl Z ι hι hfl hfp _ (bcι f ψ s _ rfl ι)
    inferInstance (bc_flat f ψ s _ rfl ι) (bc_lfp f ψ s _ rfl ι) (bcE f ψ s _ rfl ι) (isPullback_bc f ψ s _ rfl ι)
    (bc_comm f ψ s _ rfl ι)

  let skj : A →+* k := IsLocalization.Away.lift (r j) hj
  have hsk : skj.comp ψ = sk := IsLocalization.Away.lift_comp (r j) hj
  obtain ⟨x₀⟩ : Nonempty ↥(Spec (CommRingCat.of k)) := inferInstance
  have hfac : Spec.map (CommRingCat.ofHom sk) ≫ (F.pt S' s Z ι hι hfl hfp).1 =
      Spec.map (CommRingCat.ofHom skj) ≫ (F.ptC (Pj j) A (Spec.map (CommRingCat.ofHom ψ) ≫ s) _ (bcι f ψ s _ rfl ι)
        inferInstance (bc_flat f ψ s _ rfl ι) (bc_lfp f ψ s _ rfl ι) hHPj).1 ≫ Sigma.ι F.C (Pj j) := by
    rw [← hc, hn, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hsk]
  have hyQ : (Spec.map (CommRingCat.ofHom sk) ≫ (F.pt S' s Z ι hι hfl hfp).1) x₀ ∈ (Sigma.ι F.C (Pj j)).opensRange := by
    rw [hfac]
    exact ⟨_, by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]⟩
  exact F.eq_of_mem_opensRange (hmem ⟨x₀, rfl⟩) hyQ

include hX₁ hX₂ in

theorem pieces (Pℚ : Polynomial ℚ) :
    ∃ U : (∐ F.C).Opens, IsClosed (U : Set ↥(∐ F.C)) ∧ QuasiCompact (U.ι ≫ (Sigma.desc F.πC)) ∧
      ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
        (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)),
        (Set.range (F.pt S' s Z ι hι hfl hfp).1.base ⊆ (U : Set ↥(∐ F.C)) ↔
          ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              Pℚ.eval (d : ℚ)) := by
  refine ⟨(Sigma.ι F.C Pℚ).opensRange, ?_, ?_, ?_⟩
  · have h1 := (AlgebraicGeometry.Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma F.C (𝟙 (∐ F.C))).1 Pℚ
    exact h1
  · have he : (Sigma.ι F.C Pℚ).opensRange.ι ≫ Sigma.desc F.πC = (Sigma.ι F.C Pℚ).isoOpensRange.inv ≫ F.πC Pℚ := by
      rw [← Scheme.Hom.isoOpensRange_inv_comp_assoc, Sigma.ι_desc]
    rw [he]
    haveI := F.properC Pℚ
    infer_instance
  · intro S' _ s Z ι hι hfl hfp
    constructor
    · intro hsub k _ _ sk
      exact F.eventually_eq_of_range_subset hX₁ hX₂ s Z ι hι hfl hfp k sk Pℚ (by
        rintro _ ⟨x, rfl⟩
        rw [Scheme.Hom.comp_apply]
        exact hsub ⟨_, rfl⟩)
    · intro h
      rw [F.const Pℚ S' s Z ι hι hfl hfp h]
      rintro _ ⟨x, rfl⟩
      exact ⟨_, (Scheme.Hom.comp_apply _ _ x).symm⟩

end Loc
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC"

end Fam
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC"

end H1SIC
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC"

noncomputable section

namespace H1SIC

namespace Fam

variable {S : Type} [CommRing S] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of S)} {𝓛X : X.Modules} (F : Fam f 𝓛X)

section Partition

variable {S' : Type} [CommRing S'] (u : Spec (CommRingCat.of S') ⟶ ∐ F.C)

abbrev T (P : Polynomial ℚ) : (Spec (CommRingCat.of S')).Opens := u ⁻¹ᵁ (Sigma.ι F.C P).opensRange

theorem T_def (P : Polynomial ℚ) : F.T u P = u ⁻¹ᵁ (Sigma.ι F.C P).opensRange := rfl

theorem isClosed_T (P : Polynomial ℚ) : IsClosed (F.T u P : Set ↥(Spec (CommRingCat.of S'))) :=
  (AlgebraicGeometry.Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma F.C u).1 P

theorem disjoint_T (P Q : Polynomial ℚ) (h : P ≠ Q) : Disjoint (F.T u P) (F.T u Q) :=
  (AlgebraicGeometry.Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma F.C u).2.1 P Q h

theorem iSup_T : (⨆ P, F.T u P) = ⊤ :=
  (AlgebraicGeometry.Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma F.C u).2.2.1

theorem eq_of_mem_T {P Q : Polynomial ℚ} {y : ↥(Spec (CommRingCat.of S'))} (hP : y ∈ F.T u P) (hQ : y ∈ F.T u Q) :
    P = Q := by
  by_contra h
  have hd := F.disjoint_T u P Q h
  rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left] at hd
  exact hd hP hQ

theorem exists_idem (P : Polynomial ℚ) : ∃ e : S', IsIdempotentElem e ∧
    (F.T u P : Set ↥(Spec (CommRingCat.of S'))) = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum S')) :=
  PrimeSpectrum.isClopen_iff.mp ⟨F.isClosed_T u P, (F.T u P).isOpen⟩

def idem (P : Polynomial ℚ) : S' := (F.exists_idem u P).choose

theorem coe_T_eq (P : Polynomial ℚ) :
    (F.T u P : Set ↥(Spec (CommRingCat.of S'))) = (PrimeSpectrum.basicOpen (F.idem u P) : Set (PrimeSpectrum S')) :=
  (F.exists_idem u P).choose_spec.2

abbrev A (P : Polynomial ℚ) : Type := Localization.Away (F.idem u P)

abbrev ψ (P : Polynomial ℚ) : S' →+* F.A u P := algebraMap S' (F.A u P)

scoped instance isOpenImmersion_ψ (P : Polynomial ℚ) : IsOpenImmersion (Spec.map (CommRingCat.ofHom (F.ψ u P))) :=
  inferInstance

theorem range_ψ (P : Polynomial ℚ) :
    Set.range ⇑(Spec.map (CommRingCat.ofHom (F.ψ u P))) = (F.T u P : Set ↥(Spec (CommRingCat.of S'))) := by
  rw [coe_T_eq, ← PrimeSpectrum.localization_away_comap_range (F.A u P) (F.idem u P)]
  rfl

theorem opensRange_ψ (P : Polynomial ℚ) : (Spec.map (CommRingCat.ofHom (F.ψ u P))).opensRange = F.T u P :=
  TopologicalSpace.Opens.ext (F.range_ψ u P)

def isoT (P : Polynomial ℚ) : Spec (CommRingCat.of (F.A u P)) ≅ ↑(F.T u P) :=
  IsOpenImmersion.isoOfRangeEq (Spec.map (CommRingCat.ofHom (F.ψ u P))) (F.T u P).ι
    (by rw [F.range_ψ u P, Scheme.Opens.range_ι])

@[reassoc (attr := simp)]
theorem isoT_hom_ι (P : Polynomial ℚ) : (F.isoT u P).hom ≫ (F.T u P).ι = Spec.map (CommRingCat.ofHom (F.ψ u P)) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
theorem isoT_inv_ψ (P : Polynomial ℚ) : (F.isoT u P).inv ≫ Spec.map (CommRingCat.ofHom (F.ψ u P)) = (F.T u P).ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

variable (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))

abbrev sP (P : Polynomial ℚ) : Spec (CommRingCat.of (F.A u P)) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (F.ψ u P)) ≫ s

abbrev jP (P : Polynomial ℚ) : pullback f (F.sP u s P) ⟶ pullback f s := jmap f (F.ψ u P) s (F.sP u s P) rfl

theorem opensRange_jP (P : Polynomial ℚ) : (F.jP u s P).opensRange = pullback.snd f s ⁻¹ᵁ F.T u P := by
  rw [opensRange_jmap, opensRange_ψ]

theorem nonempty_isColimit_jP : Nonempty (IsColimit (Cofan.mk (pullback f s) (F.jP u s))) := by
  apply nonempty_isColimit_cofanMk_of
  · rw [show (⨆ P, (F.jP u s P).opensRange) = pullback.snd f s ⁻¹ᵁ (⨆ P, F.T u P) by
      rw [Scheme.Hom.preimage_iSup]; exact iSup_congr (fun P => F.opensRange_jP u s P), F.iSup_T u, Scheme.Hom.preimage_top]
  · intro P Q h
    change Disjoint (F.jP u s P).opensRange (F.jP u s Q).opensRange
    rw [opensRange_jP, opensRange_jP, disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.mp (F.disjoint_T u P Q h), Scheme.Hom.preimage_bot]

variable {Z : Scheme.{0}} (ι : Z ⟶ pullback f s)

abbrev ZP (P : Polynomial ℚ) : Scheme.{0} := bcObj f (F.ψ u P) s (F.sP u s P) rfl ι

abbrev ιP (P : Polynomial ℚ) : F.ZP u s ι P ⟶ pullback f (F.sP u s P) := bcι f (F.ψ u P) s (F.sP u s P) rfl ι

abbrev eP (P : Polynomial ℚ) : F.ZP u s ι P ⟶ Z := bcE f (F.ψ u P) s (F.sP u s P) rfl ι

theorem opensRange_eP (P : Polynomial ℚ) : (F.eP u s ι P).opensRange = (ι ≫ pullback.snd f s) ⁻¹ᵁ F.T u P := by
  rw [opensRange_bcE, opensRange_ψ]

theorem nonempty_isColimit_eP : Nonempty (IsColimit (Cofan.mk Z (F.eP u s ι))) := by
  apply nonempty_isColimit_cofanMk_of
  · rw [show (⨆ P, (F.eP u s ι P).opensRange) = (ι ≫ pullback.snd f s) ⁻¹ᵁ (⨆ P, F.T u P) by
      rw [Scheme.Hom.preimage_iSup]; exact iSup_congr (fun P => F.opensRange_eP u s ι P), F.iSup_T u, Scheme.Hom.preimage_top]
  · intro P Q h
    change Disjoint (F.eP u s ι P).opensRange (F.eP u s ι Q).opensRange
    rw [opensRange_eP, opensRange_eP, disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.mp (F.disjoint_T u P Q h), Scheme.Hom.preimage_bot]

end Partition
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC"

end Fam
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam"

end H1SIC
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam"

noncomputable section

namespace H1SIC

namespace Fam

variable {S : Type} [CommRing S] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of S)} {𝓛X : X.Modules} (F : Fam f 𝓛X)

section Surj

variable {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))

theorem isPullback_sigmaι_of_desc (u : Spec (CommRingCat.of S') ⟶ ∐ F.C)
    (Zf : Polynomial ℚ → Scheme.{0}) (ιf : ∀ P, Zf P ⟶ pullback f (F.sP u s P))
    (ι : (∐ Zf) ⟶ pullback f s) (hι : ∀ P, Sigma.ι Zf P ≫ ι = ιf P ≫ F.jP u s P) (P : Polynomial ℚ) :
    IsPullback (Sigma.ι Zf P) (ιf P ≫ pullback.snd f (F.sP u s P)) (ι ≫ pullback.snd f s)
      (Spec.map (CommRingCat.ofHom (F.ψ u P))) := by
  have hsq : ∀ Q, Sigma.ι Zf Q ≫ ι ≫ pullback.snd f s =
      (ιf Q ≫ pullback.snd f (F.sP u s Q)) ≫ Spec.map (CommRingCat.ofHom (F.ψ u Q)) := fun Q => by
    rw [← Category.assoc, hι, Category.assoc, jmap_snd, Category.assoc]
  refine (IsOpenImmersion.isPullback (ιf P ≫ pullback.snd f (F.sP u s P)) (Sigma.ι Zf P)
    (Spec.map (CommRingCat.ofHom (F.ψ u P))) (ι ≫ pullback.snd f s) (hsq P) ?_).flip
  ext w
  change (ι ≫ pullback.snd f s) w ∈ (Spec.map (CommRingCat.ofHom (F.ψ u P))).opensRange ↔
    w ∈ (Sigma.ι Zf P).opensRange
  constructor
  · intro hw
    rw [opensRange_ψ] at hw
    obtain ⟨Q, z, rfl⟩ := (sigmaOpenCover Zf).exists_eq w
    have hzQ : (ι ≫ pullback.snd f s) ((sigmaOpenCover Zf).f Q z) ∈ F.T u Q := by
      change (Sigma.ι Zf Q ≫ ι ≫ pullback.snd f s) z ∈ F.T u Q
      rw [hsq Q, Scheme.Hom.comp_apply, ← opensRange_ψ]
      exact ⟨_, rfl⟩
    obtain rfl := F.eq_of_mem_T u hzQ hw
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    rw [← Scheme.Hom.comp_apply, hsq P, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

theorem surj (x : SchemeHomOver s (Sigma.desc F.πC)) :
    ∃ (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
      (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)), F.pt S' s Z ι hι hfl hfp = x := by

  obtain ⟨-, -, -, hlift, -⟩ :=
    AlgebraicGeometry.Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma F.C x.1
  choose v hv using fun P => (hlift P).exists

  have hxP : ∀ P, ((F.isoT x.1 P).hom ≫ v P) ≫ F.πC P = F.sP x.1 s P := by
    intro P
    have h1 : F.πC P = Sigma.ι F.C P ≫ Sigma.desc F.πC := (Sigma.ι_desc F.πC P).symm
    have h2 : (F.T x.1 P).ι ≫ x.1 ≫ Sigma.desc F.πC = (F.T x.1 P).ι ≫ s := by rw [x.2]
    calc ((F.isoT x.1 P).hom ≫ v P) ≫ F.πC P = (F.isoT x.1 P).hom ≫ (v P ≫ Sigma.ι F.C P) ≫ Sigma.desc F.πC := by
          rw [h1]; simp only [Category.assoc]
      _ = (F.isoT x.1 P).hom ≫ ((F.T x.1 P).ι ≫ x.1) ≫ Sigma.desc F.πC := by rw [hv]
      _ = (F.isoT x.1 P).hom ≫ (F.T x.1 P).ι ≫ s := by rw [Category.assoc, h2]
      _ = F.sP x.1 s P := by rw [isoT_hom_ι_assoc]
  let xP : ∀ P, SchemeHomOver (F.sP x.1 s P) (F.πC P) := fun P => ⟨(F.isoT x.1 P).hom ≫ v P, hxP P⟩
  choose Zf ιf hιf hflf hfpf hHPf heqf using fun P => F.surjC P (F.A x.1 P) (F.sP x.1 s P) (xP P)

  obtain ⟨hX⟩ := F.nonempty_isColimit_jP x.1 s
  let φ : (∐ fun P => pullback f (F.sP x.1 s P)) ≅ pullback f s := (colimit.isColimit _).coconePointUniqueUpToIso hX
  have hφ : ∀ P, Sigma.ι (fun P => pullback f (F.sP x.1 s P)) P ≫ φ.hom = F.jP x.1 s P := fun P =>
    (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom hX ⟨P⟩

  let ι : (∐ Zf) ⟶ pullback f s := Limits.Sigma.map ιf ≫ φ.hom
  have hιι : ∀ P, Sigma.ι Zf P ≫ ι = ιf P ≫ F.jP x.1 s P := fun P => by
    simp only [ι, Sigma.ι_map_assoc, hφ]
  have hιc : IsClosedImmersion ι := by
    haveI : IsClosedImmersion (Limits.Sigma.map ιf) :=
      AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap @IsClosedImmersion ιf hιf
    infer_instance
  have hcomp : ι ≫ pullback.snd f s =
      Sigma.desc (fun P => (ιf P ≫ pullback.snd f (F.sP x.1 s P)) ≫ Spec.map (CommRingCat.ofHom (F.ψ x.1 P))) := by
    apply Sigma.hom_ext
    intro P
    rw [Sigma.ι_desc, ← Category.assoc, hιι, Category.assoc, jmap_snd, Category.assoc]
  have hιfl : Flat (ι ≫ pullback.snd f s) := by
    rw [hcomp]
    haveI := hflf
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Flat) (fun P => inferInstance)
  have hιfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s) := by
    rw [hcomp]
    haveI := hfpf
    exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation) (fun P => inferInstance)
  refine ⟨∐ Zf, ι, hιc, hιfl, hιfp, ?_⟩

  apply Subtype.ext
  obtain ⟨w, -, hwuniq⟩ := AlgebraicGeometry.Scheme.existsUnique_hom_sigma_of_disjoint_iSup_eq_top F.C (F.T x.1)
    (F.disjoint_T x.1) (F.iSup_T x.1) v
  rw [hwuniq x.1 (fun P => (hv P).symm)]
  refine hwuniq _ (fun P => ?_)
  have hn := F.nat S' (F.A x.1 P) (F.ψ x.1 P) s (F.sP x.1 s P) rfl (∐ Zf) ι hιc hιfl hιfp (Zf P) (ιf P) (hιf P)
    (hflf P) (hfpf P) (Sigma.ι Zf P) (F.isPullback_sigmaι_of_desc s x.1 Zf ιf ι hιι P) (hιι P).symm
  have hc := F.const P (F.A x.1 P) (F.sP x.1 s P) (Zf P) (ιf P) (hιf P) (hflf P) (hfpf P) (hHPf P)
  rw [heqf P] at hc
  rw [← F.isoT_inv_ψ x.1 P, Category.assoc, ← hn, hc]
  simp [xP]

end Surj
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam"

end Fam
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam"

end H1SIC
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam"

noncomputable section

namespace H1SIC

namespace Fam

variable {S : Type} [CommRing S] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of S)} {𝓛X : X.Modules} (F : Fam f 𝓛X)

section Inj

variable (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f)
  {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))

include hX₁ hX₂ in

theorem HP_piece (u : Spec (CommRingCat.of S') ⟶ ∐ F.C)
    (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
    (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) (hu : (F.pt S' s Z ι hι hfl hfp).1 = u)
    (P : Polynomial ℚ) : HP f 𝓛X (F.ιP u s ι P) P := by
  rw [HP_iff]
  intro k _ _ sk
  haveI := hι
  obtain ⟨d₀, hd⟩ := F.eventually_eq_of_range_subset hX₁ hX₂ s Z ι hι hfl hfp k (sk.comp (F.ψ u P)) P (by
    rintro _ ⟨y, rfl⟩
    rw [hu, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    have hy : (Spec.map (CommRingCat.ofHom (F.ψ u P))) ((Spec.map (CommRingCat.ofHom sk)) y) ∈ F.T u P := by
      rw [← opensRange_ψ]
      exact ⟨_, rfl⟩
    exact hy)
  exact ⟨d₀, fun d hdd => by
    rw [hval_eq_of_isPullback f 𝓛X (F.ψ u P) s _ rfl ι _ _ (isPullback_bc f (F.ψ u P) s _ rfl ι)
      (bc_comm f (F.ψ u P) s _ rfl ι)]
    exact hd d hdd⟩

include hX₁ hX₂ in

theorem inj (Z Z' : Scheme.{0}) (ι : Z ⟶ pullback f s) (ι' : Z' ⟶ pullback f s)
    (hι : IsClosedImmersion ι) (hι' : IsClosedImmersion ι')
    (hfl : Flat (ι ≫ pullback.snd f s)) (hfl' : Flat (ι' ≫ pullback.snd f s))
    (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f s))
    (heq : F.pt S' s Z ι hι hfl hfp = F.pt S' s Z' ι' hι' hfl' hfp') : ∃ e : Z ≅ Z', e.hom ≫ ι' = ι := by
  haveI := hι; haveI := hι'; haveI := hfl; haveI := hfl'; haveI := hfp; haveI := hfp'
  set u := (F.pt S' s Z ι hι hfl hfp).1 with hu
  have hHP : ∀ P, HP f 𝓛X (F.ιP u s ι P) P := F.HP_piece hX₁ hX₂ s u Z ι hι hfl hfp rfl
  have hHP' : ∀ P, HP f 𝓛X (F.ιP u s ι' P) P :=
    F.HP_piece hX₁ hX₂ s u Z' ι' hι' hfl' hfp' (congrArg Subtype.val heq).symm

  have key : ∀ P,
      F.ptC P (F.A u P) (F.sP u s P) _ (F.ιP u s ι P) inferInstance (bc_flat f (F.ψ u P) s _ rfl ι)
        (bc_lfp f (F.ψ u P) s _ rfl ι) (hHP P) =
      F.ptC P (F.A u P) (F.sP u s P) _ (F.ιP u s ι' P) inferInstance (bc_flat f (F.ψ u P) s _ rfl ι')
        (bc_lfp f (F.ψ u P) s _ rfl ι') (hHP' P) := by
    intro P
    apply Subtype.ext
    rw [← cancel_mono (Sigma.ι F.C P), ← F.const, ← F.const,
      F.nat S' (F.A u P) (F.ψ u P) s (F.sP u s P) rfl Z ι hι hfl hfp _ (F.ιP u s ι P) inferInstance
        (bc_flat f (F.ψ u P) s _ rfl ι) (bc_lfp f (F.ψ u P) s _ rfl ι) (F.eP u s ι P)
        (isPullback_bc f (F.ψ u P) s _ rfl ι) (bc_comm f (F.ψ u P) s _ rfl ι),
      F.nat S' (F.A u P) (F.ψ u P) s (F.sP u s P) rfl Z' ι' hι' hfl' hfp' _ (F.ιP u s ι' P) inferInstance
        (bc_flat f (F.ψ u P) s _ rfl ι') (bc_lfp f (F.ψ u P) s _ rfl ι') (F.eP u s ι' P)
        (isPullback_bc f (F.ψ u P) s _ rfl ι') (bc_comm f (F.ψ u P) s _ rfl ι'),
      show (F.pt S' s Z ι hι hfl hfp).1 = (F.pt S' s Z' ι' hι' hfl' hfp').1 from congrArg Subtype.val heq]
  choose eP heP using fun P => F.injC P (F.A u P) (F.sP u s P) _ _ (F.ιP u s ι P) (F.ιP u s ι' P)
    inferInstance inferInstance (bc_flat f (F.ψ u P) s _ rfl ι) (bc_flat f (F.ψ u P) s _ rfl ι')
    (bc_lfp f (F.ψ u P) s _ rfl ι) (bc_lfp f (F.ψ u P) s _ rfl ι') (hHP P) (hHP' P) (key P)

  obtain ⟨hZ⟩ := F.nonempty_isColimit_eP u s ι
  obtain ⟨hZ'⟩ := F.nonempty_isColimit_eP u s ι'
  let e : Z ≅ Z' := IsColimit.coconePointsIsoOfNatIso hZ hZ' (Discrete.natIso (fun P => eP P.as))
  refine ⟨e, hZ.hom_ext (fun P => ?_)⟩
  obtain ⟨P⟩ := P
  rw [← Category.assoc, IsColimit.comp_coconePointsIsoOfNatIso_hom, Category.assoc]
  change (eP P).hom ≫ F.eP u s ι' P ≫ ι' = F.eP u s ι P ≫ ι
  rw [← bc_comm, ← bc_comm, ← Category.assoc, heP]

end Inj
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam"

end Fam
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam"

end H1SIC
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.H1SIC.Fam"

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
            (ptC P S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptC P S' s Z ι hι hfl hfp hHP).1))
    (hsurjC : ∀ (P : Polynomial ℚ),
        (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s (πC P)),
          ∃ (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
            (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
            (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
                (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                P.eval (d : ℚ))),
            ptC P S' s Z ι hι hfl hfp hHP = x))
    (hinjC : ∀ (P : Polynomial ℚ),
        (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
            (Z Z' : Scheme.{0}) (ι : Z ⟶ pullback f s) (ι' : Z' ⟶ pullback f s)
            (hι : IsClosedImmersion ι) (hι' : IsClosedImmersion ι')
            (hfl : Flat (ι ≫ pullback.snd f s)) (hfl' : Flat (ι' ≫ pullback.snd f s))
            (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f s))
            (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
                (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                P.eval (d : ℚ)))
            (hHP' : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι' ≫ pullback.snd f s)
                (Nat.rec (motive := fun _ => Z'.Modules) (𝟙_ Z'.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι' ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                P.eval (d : ℚ))),
          ptC P S' s Z ι hι hfl hfp hHP = ptC P S' s Z' ι' hι' hfl' hfp' hHP' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι))
    (hproperC : ∀ P : Polynomial ℚ, IsProper (πC P)) (hlfpC : ∀ P : Polynomial ℚ, LocallyOfFinitePresentation (πC P))
    (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) → SchemeHomOver s (Sigma.desc πC))
    (hnat :

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
            (pt S'' s'' Z'' ι'' hι'' hfl'' hfp'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s Z ι hι hfl hfp).1))
    (hconst :

        (∀ (P : Polynomial ℚ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
            (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
            (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
            (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
                (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                P.eval (d : ℚ))),
          (pt S' s Z ι hι hfl hfp).1 = (ptC P S' s Z ι hι hfl hfp hHP).1 ≫ Sigma.ι C P)) :

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s (Sigma.desc πC)),
        ∃ (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)),
          pt S' s Z ι hι hfl hfp = x) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z Z' : Scheme.{0}) (ι : Z ⟶ pullback f s) (ι' : Z' ⟶ pullback f s)
          (hι : IsClosedImmersion ι) (hι' : IsClosedImmersion ι')
          (hfl : Flat (ι ≫ pullback.snd f s)) (hfl' : Flat (ι' ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f s)),
        pt S' s Z ι hι hfl hfp = pt S' s Z' ι' hι' hfl' hfp' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι) ∧
      IsSeparated (Sigma.desc πC) ∧ LocallyOfFinitePresentation (Sigma.desc πC) ∧

      (∀ Pℚ : Polynomial ℚ, ∃ U : (∐ C).Opens, IsClosed (U : Set ↥(∐ C)) ∧ QuasiCompact (U.ι ≫ (Sigma.desc πC)) ∧
        ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)),
          (Set.range (pt S' s Z ι hι hfl hfp).1.base ⊆ (U : Set ↥(∐ C)) ↔
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
                (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                Pℚ.eval (d : ℚ))) := by
  let F : H1SIC.Fam f 𝓛X := ⟨C, πC, ptC, hnatC, hsurjC, hinjC, hproperC, hlfpC, pt, hnat, hconst⟩
  refine ⟨fun S' _ s x => F.surj s x,
    fun S' _ s Z Z' ι ι' hι hι' hfl hfl' hfp hfp' h => F.inj hX₁ hX₂ s Z Z' ι ι' hι hι' hfl hfl' hfp hfp' h, ?_, ?_,
    fun Pℚ => F.pieces hX₁ hX₂ Pℚ⟩
  · haveI := hproperC
    exact AlgebraicGeometry.isSeparated_sigmaDesc_of_forall_isSeparated C πC (fun P => inferInstance)
  · exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation) hlfpC

end S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj
end P2MW
export P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj (solution)
