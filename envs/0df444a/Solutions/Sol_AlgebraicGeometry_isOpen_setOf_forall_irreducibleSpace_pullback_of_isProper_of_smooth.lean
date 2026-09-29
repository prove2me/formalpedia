-- Prove2me | solution 1 for AlgebraicGeometry.isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d6d983c1-a4c5-5c83-ab4a-d2505506f175

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd
import Theorems.Thm_AlgebraicGeometry_forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField
import Theorems.Thm_AlgebraicGeometry_geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace H2a2Reduce

theorem exists_noetherian_model
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) [IsProper f] [Smooth f] :
    ∃ (T : Type u) (_ : CommRing T) (_ : IsNoetherianRing T) (_ : Algebra T S)
      (Z₁ : Scheme.{u}) (f₁ : Z₁ ⟶ Spec (CommRingCat.of T)) (_ : IsProper f₁) (_ : Smooth f₁) (g₁ : Z ⟶ Z₁),
      IsPullback g₁ f f₁ (Spec.map (CommRingCat.ofHom (algebraMap T S))) := by

  let A₀ : Type u := ULift.{u} ℤ
  haveI : IsNoetherianRing A₀ := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  letI : Algebra A₀ S := ((Int.castRingHom S).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom).toAlgebra

  obtain ⟨T₀, hT₀fg, -, X₀, f₀, π, hp₀, hfl₀, hsq₀⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation
      (A₀ := A₀) f ∅
  haveI := hp₀; haveI := hfl₀
  haveI : Algebra.FiniteType A₀ T₀ := ⟨(Subalgebra.fg_top T₀).mpr hT₀fg⟩
  haveI : IsNoetherianRing T₀ := Algebra.FiniteType.isNoetherianRing A₀ T₀
  haveI : LocallyOfFinitePresentation f₀ :=
    AlgebraicGeometry.locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian f₀ (𝟙 _) f₀ (Category.comp_id _)

  haveI : Smooth (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap T₀ S)))) := by
    rw [← hsq₀.isoPullback_inv_snd]
    infer_instance

  obtain ⟨T, hTfg, -, hsmooth⟩ := AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd (A := S) f₀ ∅
  haveI : Algebra.FiniteType T₀ T := ⟨(Subalgebra.fg_top T).mpr hTfg⟩
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing T₀ T
  let locT : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of T₀) := Spec.map (CommRingCat.ofHom (algebraMap T₀ T))
  let locS : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of T) := Spec.map (CommRingCat.ofHom (algebraMap T S))
  have hcomp : locS ≫ locT = Spec.map (CommRingCat.ofHom (algebraMap T₀ S)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hring : (algebraMap (↥T) S).comp (algebraMap (↥T₀) (↥T)) = algebraMap (↥T₀) S := RingHom.ext fun x => rfl
    rw [hring]
  let g₁ : Z ⟶ pullback f₀ locT := pullback.lift π (f ≫ locS) (by rw [Category.assoc, hcomp, hsq₀.w])
  refine ⟨T, inferInstance, inferInstance, inferInstance, pullback f₀ locT, pullback.snd f₀ locT, inferInstance, hsmooth, g₁, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst f₀ locT) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f₀ locT)
  rw [pullback.lift_fst, hcomp]
  exact hsq₀

theorem geometricallyIrreducible_fiber_of_isPullback
    {S T : Type u} [CommRing S] [CommRing T] (φ : T →+* S)
    {Z Z₁ : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) (f₁ : Z₁ ⟶ Spec (CommRingCat.of T)) (g₁ : Z ⟶ Z₁)
    (h : IsPullback g₁ f f₁ (Spec.map (CommRingCat.ofHom φ))) (s : ↥(Spec (CommRingCat.of S)))
    [hs : GeometricallyIrreducible (f.fiberToSpecResidueField s)] :
    GeometricallyIrreducible (f₁.fiberToSpecResidueField ((Spec.map (CommRingCat.ofHom φ)).base s)) := by
  classical
  have hsq := isPullback_fiberToSpecResidueField_of_isPullback h s

  let k : Type u := AlgebraicClosure ↑((Spec (CommRingCat.of S)).residueField s)
  let inst : Algebra ↑((Spec (CommRingCat.of T)).residueField ((Spec.map (CommRingCat.ofHom φ)).base s)) k :=
    ((algebraMap ↑((Spec (CommRingCat.of S)).residueField s) k).comp
      ((Spec.map (CommRingCat.ofHom φ)).residueFieldMap s).hom).toAlgebra
  letI := inst
  have hab : Spec.map (CommRingCat.ofHom (algebraMap ↑((Spec (CommRingCat.of T)).residueField ((Spec.map (CommRingCat.ofHom φ)).base s)) k))
      = Spec.map (CommRingCat.ofHom (algebraMap ↑((Spec (CommRingCat.of S)).residueField s) k)) ≫
        Spec.map ((Spec.map (CommRingCat.ofHom φ)).residueFieldMap s) := by
    rw [← Spec.map_comp]; rfl

  have hirr' : IrreducibleSpace ↑(pullback (f₁.fiberToSpecResidueField ((Spec.map (CommRingCat.ofHom φ)).base s))
      (Spec.map (CommRingCat.ofHom (algebraMap ↑((Spec (CommRingCat.of S)).residueField s) k)) ≫
        Spec.map ((Spec.map (CommRingCat.ofHom φ)).residueFieldMap s))) := by
    have houter := IsPullback.of_hasPullback (f₁.fiberToSpecResidueField ((Spec.map (CommRingCat.ofHom φ)).base s))
      (Spec.map (CommRingCat.ofHom (algebraMap ↑((Spec (CommRingCat.of S)).residueField s) k)) ≫
        Spec.map ((Spec.map (CommRingCat.ofHom φ)).residueFieldMap s))
    obtain ⟨l, hl₁, hl₂⟩ : ∃ l, l ≫ _ = pullback.fst _ _ ∧ l ≫ f.fiberToSpecResidueField s = pullback.snd _ _ ≫ _ :=
      ⟨hsq.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↑((Spec (CommRingCat.of S)).residueField s) k)))
        (by rw [Category.assoc]; exact pullback.condition), hsq.lift_fst _ _ _, hsq.lift_snd _ _ _⟩
    have hleft := (IsPullback.paste_horiz_iff hsq hl₂).mp (hl₁.symm ▸ houter)
    exact hs.geometrically_irreducibleSpace _ l (pullback.snd _ _) hleft
  have hirr : IrreducibleSpace ↑(pullback (f₁.fiberToSpecResidueField ((Spec.map (CommRingCat.ofHom φ)).base s))
      (Spec.map (CommRingCat.ofHom (algebraMap ↑((Spec (CommRingCat.of T)).residueField ((Spec.map (CommRingCat.ofHom φ)).base s)) k)))) := by
    exact hab ▸ hirr'
  exact @AlgebraicGeometry.geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed _ _ _
    (f₁.fiberToSpecResidueField ((Spec.map (CommRingCat.ofHom φ)).base s)) k _ inst _ hirr

theorem geometricallyIrreducible_fiber_of_isPullback'
    {S T : Type u} [CommRing S] [CommRing T] (φ : T →+* S)
    {Z Z₁ : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) (f₁ : Z₁ ⟶ Spec (CommRingCat.of T)) (g₁ : Z ⟶ Z₁)
    (h : IsPullback g₁ f f₁ (Spec.map (CommRingCat.ofHom φ))) (s : ↥(Spec (CommRingCat.of S)))
    [GeometricallyIrreducible (f₁.fiberToSpecResidueField ((Spec.map (CommRingCat.ofHom φ)).base s))] :
    GeometricallyIrreducible (f.fiberToSpecResidueField s) := by
  have hsq := isPullback_fiberToSpecResidueField_of_isPullback h s
  exact MorphismProperty.of_isPullback (P := @GeometricallyIrreducible) hsq (by assumption)

theorem main
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) [IsProper f] [Smooth f] :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))} := by
  obtain ⟨T, _, _, _, Z₁, f₁, _, _, g₁, hsq⟩ := exists_noetherian_model f
  have hU₁ := AlgebraicGeometry.isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth_of_isNoetherianRing f₁
  have hEq : {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))}
      = (Spec.map (CommRingCat.ofHom (algebraMap T S))).base ⁻¹'
        {t : ↥(Spec (CommRingCat.of T)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : T →+* k),
          RingHom.ker x = t.asIdeal → IrreducibleSpace ↥(pullback f₁ (Spec.map (CommRingCat.ofHom x)))} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [AlgebraicGeometry.forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField f s,
      AlgebraicGeometry.forall_irreducibleSpace_pullback_iff_geometricallyIrreducible_fiberToSpecResidueField f₁ _]
    exact ⟨fun _ => geometricallyIrreducible_fiber_of_isPullback (algebraMap T S) f f₁ g₁ hsq s,
      fun _ => geometricallyIrreducible_fiber_of_isPullback' (algebraMap T S) f f₁ g₁ hsq s⟩
  rw [hEq]
  exact hU₁.preimage (Spec.map (CommRingCat.ofHom (algebraMap T S))).continuous

end H2a2Reduce

theorem solution
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S)) [IsProper f] [Smooth f] :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))} :=
  H2a2Reduce.main f

end S_AlgebraicGeometry_isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth
end P2MW
export P2MW.S_AlgebraicGeometry_isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth (solution)
