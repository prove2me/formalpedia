-- Prove2me | solution 1 for AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c130d7a7-34ca-5c6c-8f16-df0d813c62a4

import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd
import Theorems.Thm_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd
import Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace NoethModel17

section Compare

variable {R₁ : Type u} [CommRing R₁] {L : Type u} [CommRing L] [Algebra R₁ L] (T : Subalgebra R₁ L)
  {A₁ : Scheme.{u}} (f₁ : A₁ ⟶ Spec (CommRingCat.of R₁))

theorem specMap_val_comp :
    Spec.map (CommRingCat.ofHom T.val.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T)) =
      Spec.map (CommRingCat.ofHom (algebraMap R₁ L)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem exists_transition :
    ∃ r : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ L))) ⟶
        pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))),
      r ≫ pullback.fst f₁ _ = pullback.fst f₁ _ ∧
      r ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) :=
  ⟨pullback.lift (pullback.fst f₁ _) (pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom))
      (by rw [Category.assoc, specMap_val_comp]; exact pullback.condition),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

variable {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of L)} (π : X ⟶ A₁)
  (hπ : IsPullback π p f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ L))))

theorem isPullback_comp_transition
    (r : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ L))) ⟶
        pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))))
    (hr_fst : r ≫ pullback.fst f₁ _ = pullback.fst f₁ _)
    (hr_snd : r ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom)) :
    IsPullback (hπ.isoPullback.hom ≫ r) p (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))))
      (Spec.map (CommRingCat.ofHom T.val.toRingHom)) := by
  have hg_fst : (hπ.isoPullback.hom ≫ r) ≫ pullback.fst f₁ _ = π := by
    rw [Category.assoc, hr_fst, hπ.isoPullback_hom_fst]
  have hg_snd : (hπ.isoPullback.hom ≫ r) ≫ pullback.snd f₁ _ = p ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) := by
    rw [Category.assoc, hr_snd, ← Category.assoc, hπ.isoPullback_hom_snd]
  refine IsPullback.of_right (h₁₂ := pullback.fst f₁ _) (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap R₁ ↥T))) (v₁₃ := f₁)
    ?_ hg_snd (IsPullback.of_hasPullback f₁ _)
  rw [hg_fst, specMap_val_comp]; exact hπ

end Compare

theorem fg_restrictScalars {L : Type u} [CommRing L] (R₁ : Subalgebra ℤ L) (T : Subalgebra ↥R₁ L)
    (h₁ : R₁.FG) (h₂ : T.FG) : (T.restrictScalars ℤ).FG := by
  have i1 : Algebra.FiniteType ℤ ↥R₁ := (Subalgebra.fg_iff_finiteType _).1 h₁
  have i2 : Algebra.FiniteType ↥R₁ ↥T := (Subalgebra.fg_iff_finiteType _).1 h₂
  have i3 : Algebra.FiniteType ℤ ↥T := Algebra.FiniteType.trans i1 i2
  exact (Subalgebra.fg_iff_finiteType (T.restrictScalars ℤ)).2 i3

theorem isNoetherianRing_of_fg {L : Type u} [CommRing L] (R : Subalgebra ℤ L) (hR : R.FG) : IsNoetherianRing ↥R := by
  haveI : Algebra.FiniteType ℤ ↥R := (Subalgebra.fg_iff_finiteType _).1 hR
  exact Algebra.FiniteType.isNoetherianRing ℤ ↥R

variable {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))

theorem prop_snd_of_isPullback (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {R : Type u} [CommRing R] [Algebra R S] {X : Scheme.{u}} {f₁ : X ⟶ Spec (CommRingCat.of R)} {c : Z ⟶ X}
    (hc : IsPullback c f f₁ (Spec.map (CommRingCat.ofHom (algebraMap R S)))) (hf : P f) :
    P (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap R S)))) := by
  have h : pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap R S))) = hc.isoPullback.inv ≫ f := by
    rw [Iso.eq_inv_comp, hc.isoPullback_hom_snd]
  rw [h]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).2 hf

theorem prop_snd (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] {X Y W : Scheme.{u}}
    (f₁ : X ⟶ W) (g : Y ⟶ W) (hP : P f₁) : P (pullback.snd f₁ g) :=
  MorphismProperty.pullback_snd _ _ hP

def IsModel (R : Subalgebra ℤ S) {X : Scheme.{u}} (f₁ : X ⟶ Spec (CommRingCat.of ↥R)) (c : Z ⟶ X) : Prop :=
  IsPullback c f f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R S)))

theorem step (R : Subalgebra ℤ S) {X : Scheme.{u}} (f₁ : X ⟶ Spec (CommRingCat.of ↥R)) (c : Z ⟶ X)
    (hc : IsModel f R f₁ c) (T : Subalgebra ↥R S) :
    ∃ c' : Z ⟶ pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))),
      IsModel f (T.restrictScalars ℤ)
        (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))) :
          pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))) ⟶ Spec (CommRingCat.of ↥(T.restrictScalars ℤ))) c' := by
  obtain ⟨r, hr₁, hr₂⟩ := exists_transition T f₁
  exact ⟨_, isPullback_comp_transition T f₁ c hc r hr₁ hr₂⟩

theorem stage_sep (R : Subalgebra ℤ S) (hR : R.FG) {X : Scheme.{u}} (f₁ : X ⟶ Spec (CommRingCat.of ↥R)) (c : Z ⟶ X)
    (hc : IsModel f R f₁ c) [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₁] [IsSeparated f] :
    ∃ (R' : Subalgebra ℤ S) (_ : R'.FG) (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of ↥R')) (c' : Z ⟶ X'),
      IsModel f R' f' c' ∧ IsSeparated f' ∧ QuasiCompact f' ∧ LocallyOfFinitePresentation f' := by
  haveI : IsSeparated (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R S)))) :=
    prop_snd_of_isPullback f @IsSeparated hc inferInstance
  obtain ⟨T, hT, -, hT'⟩ := AlgebraicGeometry.IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd (A := S) f₁ (∅ : Finset S)
  obtain ⟨c', hc'⟩ := step f R f₁ c hc T
  exact ⟨T.restrictScalars ℤ, fg_restrictScalars R T hR hT, _, _, c', hc', hT',
    prop_snd @QuasiCompact f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))) inferInstance,
    prop_snd @LocallyOfFinitePresentation f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))) inferInstance⟩

theorem stage_proper (R : Subalgebra ℤ S) (hR : R.FG) {X : Scheme.{u}} (f₁ : X ⟶ Spec (CommRingCat.of ↥R)) (c : Z ⟶ X)
    (hc : IsModel f R f₁ c) [IsSeparated f₁] [QuasiCompact f₁] [LocallyOfFinitePresentation f₁] [IsProper f] :
    ∃ (R' : Subalgebra ℤ S) (_ : R'.FG) (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of ↥R')) (c' : Z ⟶ X'),
      IsModel f R' f' c' ∧ IsProper f' ∧ LocallyOfFinitePresentation f' := by
  haveI : IsNoetherianRing ↥R := isNoetherianRing_of_fg R hR
  haveI : IsProper (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R S)))) :=
    prop_snd_of_isPullback f @IsProper hc inferInstance
  obtain ⟨T, hT, -, hT'⟩ := AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd (A := S) f₁ (∅ : Finset S)
  obtain ⟨c', hc'⟩ := step f R f₁ c hc T
  exact ⟨T.restrictScalars ℤ, fg_restrictScalars R T hR hT, _, _, c', hc', hT',
    prop_snd @LocallyOfFinitePresentation f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))) inferInstance⟩

theorem stage_smooth (R : Subalgebra ℤ S) (hR : R.FG) {X : Scheme.{u}} (f₁ : X ⟶ Spec (CommRingCat.of ↥R)) (c : Z ⟶ X)
    (hc : IsModel f R f₁ c) [IsProper f₁] [LocallyOfFinitePresentation f₁] [Smooth f] :
    ∃ (R' : Subalgebra ℤ S) (_ : R'.FG) (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of ↥R')) (c' : Z ⟶ X'),
      IsModel f R' f' c' ∧ IsProper f' ∧ Smooth f' := by
  haveI : Smooth (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R S)))) :=
    prop_snd_of_isPullback f @Smooth hc inferInstance
  obtain ⟨T, hT, -, hT'⟩ := AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd (A := S) f₁ (∅ : Finset S)
  obtain ⟨c', hc'⟩ := step f R f₁ c hc T
  exact ⟨T.restrictScalars ℤ, fg_restrictScalars R T hR hT, _, _, c', hc',
    prop_snd @IsProper f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))) inferInstance, hT'⟩

theorem stage_gc (R : Subalgebra ℤ S) (hR : R.FG) {X : Scheme.{u}} (f₁ : X ⟶ Spec (CommRingCat.of ↥R)) (c : Z ⟶ X)
    (hc : IsModel f R f₁ c) [IsProper f₁] [Smooth f₁] [GeometricallyConnected f] :
    ∃ (R' : Subalgebra ℤ S) (_ : R'.FG) (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of ↥R')) (c' : Z ⟶ X'),
      IsModel f R' f' c' ∧ IsProper f' ∧ Smooth f' ∧ GeometricallyConnected f' := by
  haveI : IsNoetherianRing ↥R := isNoetherianRing_of_fg R hR
  haveI : GeometricallyConnected (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R S)))) :=
    prop_snd_of_isPullback f @GeometricallyConnected hc inferInstance
  obtain ⟨T, hT, -, hT'⟩ := AlgebraicGeometry.GeometricallyConnected.exists_fg_subalgebra_of_geometricallyConnected_pullback_snd (A := S) f₁ (∅ : Finset S)
  obtain ⟨c', hc'⟩ := step f R f₁ c hc T
  exact ⟨T.restrictScalars ℤ, fg_restrictScalars R T hR hT, _, _, c', hc',
    prop_snd @IsProper f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))) inferInstance,
    prop_snd @Smooth f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥R ↥T))) inferInstance, hT'⟩

attribute [local instance] ULift.algebra' in

theorem stage0 [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f] :
    ∃ (R' : Subalgebra ℤ S) (_ : R'.FG) (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of ↥R')) (c' : Z ⟶ X'),
      IsModel f R' f' c' ∧ QuasiCompact f' ∧ QuasiSeparated f' ∧ LocallyOfFinitePresentation f' := by
  obtain ⟨T, hT, -, X', f', c', hlfp, hqc, hqs, hc'⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation (A₀ := ULift.{u} ℤ) (A := S) f (∅ : Finset S)
  have i1 : Algebra.FiniteType ℤ (ULift.{u} ℤ) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId ℤ (ULift.{u} ℤ)) (fun x => ⟨x.down, rfl⟩)
  have i2 : Algebra.FiniteType (ULift.{u} ℤ) ↥T := (Subalgebra.fg_iff_finiteType _).1 hT
  have i3 : Algebra.FiniteType ℤ ↥T := Algebra.FiniteType.trans i1 i2
  exact ⟨T.restrictScalars ℤ, (Subalgebra.fg_iff_finiteType (T.restrictScalars ℤ)).2 i3, X', f', c', hc', hqc, hqs, hlfp⟩

end NoethModel17

open NoethModel17 in
theorem solution
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hsm : Smooth f) (hpr : IsProper f)
    (hconn : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))) :
    ∃ (S₁ : Subalgebra ℤ S) (_ : S₁.FG) (Z₁ : Scheme.{u}) (f₁ : Z₁ ⟶ Spec (CommRingCat.of ↥S₁)) (g₁ : Z ⟶ Z₁),
      IsPullback g₁ f f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ S))) ∧
      Smooth f₁ ∧ IsProper f₁ ∧ GeometricallyConnected f₁ := by
  haveI := hsm
  haveI := hpr
  haveI : GeometricallyConnected f :=
    AlgebraicGeometry.geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed f hconn

  obtain ⟨R₀, hR₀, X₀, f₀, c₀, hc₀, hqc₀, hqs₀, hlfp₀⟩ := stage0 f
  haveI := hlfp₀; haveI := hqc₀; haveI := hqs₀

  obtain ⟨R₁, hR₁, X₁, f₁, c₁, hc₁, hsep₁, hqc₁, hlfp₁⟩ := stage_sep f R₀ hR₀ f₀ c₀ hc₀
  haveI := hsep₁; haveI := hqc₁; haveI := hlfp₁

  obtain ⟨R₂, hR₂, X₂, f₂, c₂, hc₂, hpr₂, hlfp₂⟩ := stage_proper f R₁ hR₁ f₁ c₁ hc₁
  haveI := hpr₂; haveI := hlfp₂

  obtain ⟨R₃, hR₃, X₃, f₃, c₃, hc₃, hpr₃, hsm₃⟩ := stage_smooth f R₂ hR₂ f₂ c₂ hc₂
  haveI := hpr₃; haveI := hsm₃

  obtain ⟨R₄, hR₄, X₄, f₄, c₄, hc₄, hpr₄, hsm₄, hgc₄⟩ := stage_gc f R₃ hR₃ f₃ c₃ hc₃
  exact ⟨R₄, hR₄, X₄, f₄, c₄, hc₄, hsm₄, hpr₄, hgc₄⟩

end S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected
end P2MW
export P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected (solution)
