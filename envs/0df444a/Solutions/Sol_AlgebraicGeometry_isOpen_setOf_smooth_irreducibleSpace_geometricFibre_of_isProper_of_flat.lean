-- Prove2me | solution 1 for AlgebraicGeometry.isOpen_setOf_smooth_irreducibleSpace_geometricFibre_of_isProper_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/acbc8438-6e53-5365-a2b1-187db85af070

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_isOpen_setOf_forall_smooth_pullback_snd_of_universallyClosed_of_flat
import Theorems.Thm_AlgebraicGeometry_isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth
import Theorems.Thm_AlgebraicGeometry_isOpen_setOf_forall_topologicalKrullDim_pullback_eq_of_isProper_of_smooth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isOpen_setOf_smooth_irreducibleSpace_geometricFibre_of_isProper_of_flat
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace H2a

theorem smooth_pullback_snd_of_range_subset {Z Y T : Scheme.{u}} (f : Z ⟶ Y) (V : Y.Opens) [Smooth (f ∣_ V)]
    (t : T ⟶ Y) (ht : Set.range t.base ⊆ (V : Set ↥Y)) : Smooth (pullback.snd f t) := by
  have hrange : Set.range t.base ⊆ Set.range V.ι.base := by rwa [Scheme.Opens.range_ι]
  let y := IsOpenImmersion.lift V.ι t hrange
  have hy : y ≫ V.ι = t := IsOpenImmersion.lift_fac _ _ _
  have houter : IsPullback (pullback.fst f t) (pullback.snd f t) f (y ≫ V.ι) := by
    rw [hy]; exact IsPullback.of_hasPullback _ _
  have hl : Set.range (pullback.fst f t).base ⊆ Set.range (f ⁻¹ᵁ V).ι.base := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hc := congrArg (fun φ => φ.base q) (pullback.condition (f := f) (g := t))
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hc
    change f.base ((pullback.fst f t).base q) ∈ V
    rw [hc]
    exact ht ⟨_, rfl⟩
  let s := IsOpenImmersion.lift (f ⁻¹ᵁ V).ι (pullback.fst f t) hl
  have hs : s ≫ (f ⁻¹ᵁ V).ι = pullback.fst f t := IsOpenImmersion.lift_fac _ _ _
  have hsq : IsPullback s (pullback.snd f t) (f ∣_ V) y := by
    refine IsPullback.of_right (by rw [hs]; exact houter) ?_ (isPullback_morphismRestrict f V).flip
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc, hs, hy, pullback.condition]
  exact MorphismProperty.of_isPullback (P := @Smooth) hsq inferInstance

section Transfer

variable {S S' k : Type u} [CommRing S] [CommRing S'] [CommRing k] {Z : Scheme.{u}}
  (f : Z ⟶ Spec (CommRingCat.of S)) (φ : S →+* S') (x' : S' →+* k)

noncomputable def fibreIso :
    pullback f (Spec.map (CommRingCat.ofHom (x'.comp φ))) ≅
      pullback (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (Spec.map (CommRingCat.ofHom x')) :=
  pullback.congrHom rfl (by rw [CommRingCat.ofHom_comp, Spec.map_comp]) ≪≫
    (pullbackLeftPullbackSndIso f (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom x'))).symm

private theorem _root_.H2a.irreducibleSpace_iff :
    IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (x'.comp φ)))) ↔
      IrreducibleSpace ↥(pullback (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (Spec.map (CommRingCat.ofHom x'))) :=
  (Scheme.homeoOfIso (fibreIso f φ x')).irreducibleSpace_iff

p2m_export "H2a" "irreducibleSpace_iff"
private theorem _root_.H2a.topologicalKrullDim_eq :
    topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom (x'.comp φ)))) =
      topologicalKrullDim ↥(pullback (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (Spec.map (CommRingCat.ofHom x'))) :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (fibreIso f φ x')).isHomeomorph

p2m_export "H2a" "topologicalKrullDim_eq"
end Transfer

variable {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))

theorem ker_comp_eq {S' k : Type u} [CommRing S'] [Field k] (φ : S →+* S') (x' : S' →+* k) :
    RingHom.ker (x'.comp φ) = ((Spec.map (CommRingCat.ofHom φ)).base ⟨RingHom.ker x', RingHom.ker_isPrime x'⟩).asIdeal := by
  rw [Spec.map_apply]
  show RingHom.ker (x'.comp φ) = (PrimeSpectrum.comap φ ⟨RingHom.ker x', RingHom.ker_isPrime x'⟩).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, RingHom.comap_ker]

theorem exists_lift_away (r : S) {k : Type u} [Field k] (x : S →+* k) (hx : r ∉ RingHom.ker x) :
    ∃ x' : Localization.Away r →+* k, x'.comp (algebraMap S (Localization.Away r)) = x := by
  have hu : IsUnit (x r) := by
    rw [RingHom.mem_ker] at hx
    exact isUnit_iff_ne_zero.mpr hx
  exact ⟨IsLocalization.Away.lift r hu, IsLocalization.Away.lift_comp r hu⟩

def P (g : ℕ) (s : ↥(Spec (CommRingCat.of S))) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k), RingHom.ker x = s.asIdeal →
    Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
    IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
    topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g

theorem main [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (g : ℕ) :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | P f g s} ∧
    ∀ V : (Spec (CommRingCat.of S)).Opens, (V : Set ↥(Spec (CommRingCat.of S))) ⊆ {s | P f g s} → Smooth (f ∣_ V) := by

  obtain ⟨hU₁open, hU₁smooth⟩ :=
    AlgebraicGeometry.isOpen_setOf_forall_smooth_pullback_snd_of_universallyClosed_of_flat f
  let U₁ : (Spec (CommRingCat.of S)).Opens := ⟨_, hU₁open⟩
  have hPU₁ : {s : ↥(Spec (CommRingCat.of S)) | P f g s} ⊆ (U₁ : Set _) :=
    fun s hs k _ _ x hx => (hs k x hx).1
  refine ⟨?_, fun V hV => hU₁smooth V (hV.trans hPU₁)⟩
  haveI : Smooth (f ∣_ U₁) := hU₁smooth U₁ le_rfl
  rw [isOpen_iff_forall_mem_open]
  intro s hs

  obtain ⟨_, ⟨r, rfl⟩, hsr, hrU₁⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (hPU₁ hs) U₁.2
  let S₁ := Localization.Away r
  let loc₁ : Spec (CommRingCat.of S₁) ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S S₁))
  have hrange₁ : Set.range loc₁.base = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum S)) := by
    show Set.range (PrimeSpectrum.comap (algebraMap S S₁)) = _
    exact PrimeSpectrum.localization_away_comap_range S₁ r
  let f₁ := pullback.snd f loc₁
  haveI : Smooth f₁ := smooth_pullback_snd_of_range_subset f U₁ loc₁ (hrange₁ ▸ hrU₁)

  have hU₂open := AlgebraicGeometry.isOpen_setOf_forall_irreducibleSpace_pullback_of_isProper_of_smooth f₁

  let U₂ : Set ↥(Spec (CommRingCat.of S)) := loc₁.base ''
    {s₁ | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S₁ →+* k), RingHom.ker x = s₁.asIdeal →
      IrreducibleSpace ↥(pullback f₁ (Spec.map (CommRingCat.ofHom x)))}
  have hU₂open' : IsOpen U₂ := loc₁.isOpenEmbedding.isOpenMap _ hU₂open
  have hsU₂ : s ∈ U₂ := by
    obtain ⟨s₁, hs₁⟩ : s ∈ Set.range loc₁.base := by rw [hrange₁]; exact hsr
    refine ⟨s₁, fun k _ _ x' hx' => ?_, hs₁⟩
    have hker : RingHom.ker (x'.comp (algebraMap S S₁)) = s.asIdeal := by
      rw [ker_comp_eq, ← hs₁]; congr 2; exact PrimeSpectrum.ext hx'
    exact (irreducibleSpace_iff f (algebraMap S S₁) x').mp (hs k _ hker).2.1

  have hU₂irr : ∀ t ∈ U₂, ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k), RingHom.ker x = t.asIdeal →
      IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) := by
    rintro t ⟨t₁, ht₁, rfl⟩ k _ _ x hx
    have hr : r ∉ RingHom.ker x := by
      rw [hx]; show loc₁.base t₁ ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum S))
      rw [← hrange₁]; exact ⟨t₁, rfl⟩
    obtain ⟨x', rfl⟩ := exists_lift_away r x hr
    have ht₁' : (⟨RingHom.ker x', RingHom.ker_isPrime x'⟩ : PrimeSpectrum S₁) = t₁ := by
      apply PrimeSpectrum.localization_comap_injective (S := S₁) (Submonoid.powers r)
      apply PrimeSpectrum.ext
      have := ker_comp_eq (algebraMap S S₁) x'
      rw [hx, Spec.map_apply] at this
      exact this.symm
    exact (irreducibleSpace_iff f (algebraMap S S₁) x').mpr (ht₁ k x' (by rw [← ht₁']))

  obtain ⟨_, ⟨r₂, rfl⟩, hsr₂, hr₂U₂⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hsU₂ hU₂open'
  let S₂ := Localization.Away r₂
  let loc₂ : Spec (CommRingCat.of S₂) ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S S₂))
  have hrange₂ : Set.range loc₂.base = (PrimeSpectrum.basicOpen r₂ : Set (PrimeSpectrum S)) := by
    show Set.range (PrimeSpectrum.comap (algebraMap S S₂)) = _
    exact PrimeSpectrum.localization_away_comap_range S₂ r₂
  have hU₂U₁ : U₂ ⊆ (U₁ : Set _) := by
    rintro _ ⟨t₁, -, rfl⟩; apply hrU₁; beta_reduce; rw [← hrange₁]; exact ⟨t₁, rfl⟩
  let f₂ := pullback.snd f loc₂
  haveI : Smooth f₂ := smooth_pullback_snd_of_range_subset f U₁ loc₂ (hrange₂ ▸ (hr₂U₂.trans hU₂U₁))
  have hirr₂ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S₂ →+* k),
      IrreducibleSpace ↥(pullback f₂ (Spec.map (CommRingCat.ofHom x))) := by
    intro k _ _ x'
    refine (irreducibleSpace_iff f (algebraMap S S₂) x').mp (hU₂irr _ ?_ k _ (ker_comp_eq (algebraMap S S₂) x'))
    apply hr₂U₂; beta_reduce; rw [← hrange₂]; exact ⟨_, rfl⟩

  have hU₃open := AlgebraicGeometry.isOpen_setOf_forall_topologicalKrullDim_pullback_eq_of_isProper_of_smooth f₂ hirr₂ g
  let U₃ : Set ↥(Spec (CommRingCat.of S)) := loc₂.base ''
    {s₂ | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S₂ →+* k), RingHom.ker x = s₂.asIdeal →
      topologicalKrullDim ↥(pullback f₂ (Spec.map (CommRingCat.ofHom x))) = g}
  refine ⟨U₃, ?_, loc₂.isOpenEmbedding.isOpenMap _ hU₃open, ?_⟩
  ·
    rintro t ⟨t₂, ht₂, rfl⟩ k _ _ x hx
    have htU₂ : loc₂.base t₂ ∈ U₂ := by apply hr₂U₂; beta_reduce; rw [← hrange₂]; exact ⟨t₂, rfl⟩
    refine ⟨(hU₂U₁ htU₂) k x hx, hU₂irr _ htU₂ k x hx, ?_⟩
    have hr : r₂ ∉ RingHom.ker x := by
      rw [hx]; show loc₂.base t₂ ∈ (PrimeSpectrum.basicOpen r₂ : Set (PrimeSpectrum S))
      rw [← hrange₂]; exact ⟨t₂, rfl⟩
    obtain ⟨x', rfl⟩ := exists_lift_away r₂ x hr
    have ht₂' : (⟨RingHom.ker x', RingHom.ker_isPrime x'⟩ : PrimeSpectrum S₂) = t₂ := by
      apply PrimeSpectrum.localization_comap_injective (S := S₂) (Submonoid.powers r₂)
      apply PrimeSpectrum.ext
      have := ker_comp_eq (algebraMap S S₂) x'
      rw [hx, Spec.map_apply] at this
      exact this.symm
    rw [topologicalKrullDim_eq f (algebraMap S S₂) x']
    exact ht₂ k x' (by rw [← ht₂'])
  ·
    obtain ⟨s₂, hs₂⟩ : s ∈ Set.range loc₂.base := by rw [hrange₂]; exact hsr₂
    refine ⟨s₂, fun k _ _ x' hx' => ?_, hs₂⟩
    have hker : RingHom.ker (x'.comp (algebraMap S S₂)) = s.asIdeal := by
      rw [ker_comp_eq, ← hs₂]; congr 2; exact PrimeSpectrum.ext hx'
    rw [← topologicalKrullDim_eq f (algebraMap S S₂) x']
    exact (hs k _ hker).2.2

end H2a

theorem solution
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (g : ℕ) :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g} ∧
    ∀ V : (Spec (CommRingCat.of S)).Opens,
      (V : Set ↥(Spec (CommRingCat.of S))) ⊆ {s | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g} →
      Smooth (f ∣_ V) :=
  H2a.main f g

end S_AlgebraicGeometry_isOpen_setOf_smooth_irreducibleSpace_geometricFibre_of_isProper_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_isOpen_setOf_smooth_irreducibleSpace_geometricFibre_of_isProper_of_flat (solution)
