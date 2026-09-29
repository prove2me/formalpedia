-- Prove2me | solution 1 for AlgebraicGeometry.exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/185e05cd-a49c-5e0e-89a7-6bf70c7a6686

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_exists_isClopen_preimage_eq_of_isProper_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace ProperClopenNbhd

section ClosedPointOfField

variable {R : Type u} [CommRing R] [IsLocalRing R] {K : Type u} [Field K]
  (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion ι]

lemma surjective_preimage : Function.Surjective (Spec.preimage ι).hom := by
  have h : Function.Surjective (ι.appTop) := ι.app_surjective ⊤ (isAffineOpen_top _)
  have hnat := Scheme.ΓSpecIso_naturality (Spec.preimage ι)
  rw [Spec.map_preimage] at hnat
  have heq : (Spec.preimage ι) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ι.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [hnat, Iso.inv_hom_id_assoc]
  have hsurj : Function.Surjective
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ι.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom := by
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.surjective.comp h).comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.surjective
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, by rw [heq]; exact hx⟩

lemma apply_eq_closedPoint (z : Spec (CommRingCat.of K)) : ι z = closedPoint R := by
  have hι : ι = Spec.map (Spec.preimage ι) := (Spec.map_preimage ι).symm
  rw [hι]
  apply PrimeSpectrum.ext
  change Ideal.comap (Spec.preimage ι).hom z.asIdeal = maximalIdeal R
  have hz : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top z.asIdeal).resolve_right z.isPrime.ne_top
  rw [hz, ← RingHom.ker_eq_comap_bot]
  exact IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective _ (surjective_preimage ι))

lemma closedPoint_mem_range : closedPoint R ∈ Set.range ι :=
  ⟨closedPoint K, apply_eq_closedPoint ι _⟩

lemma exists_mem_of_isClosed {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed q] {C : Set P} (hC : IsClosed C) {w : P} (hw : w ∈ C) :
    ∃ w' ∈ C, q w' ∈ Set.range ι := by
  have hcl : IsClosed (q '' closure {w}) := q.isClosedMap _ isClosed_closure
  have hmem : closedPoint R ∈ q '' closure {w} := by
    have hspec : q w ⤳ closedPoint R := IsLocalRing.specializes_closedPoint (q w)
    exact hspec.mem_closed hcl ⟨w, subset_closure rfl, rfl⟩
  obtain ⟨w', hw', hqw'⟩ := hmem
  exact ⟨w', (hC.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hw)) hw',
    hqw' ▸ closedPoint_mem_range ι⟩

end ClosedPointOfField

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A))
  [IsClosedImmersion ι] [IsProper (pullback.snd f ι)]

  {X' P : Scheme.{u}} (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A))
  [IsProper π] [Surjective π] [IsOpenImmersion j] [IsProper q] (hcomm : j ≫ q = π ≫ f)

noncomputable abbrev pP := pullback.fst q ι

noncomputable abbrev j₀ := pullback.snd j (pP ι q)

include hcomm in

lemma isProper_j₀_comp : IsProper (j₀ ι j q ≫ pullback.snd q ι) := by

  have h1 : IsProper (pullback.snd (π ≫ f) ι) := by
    have : IsProper ((pullbackRightPullbackFstIso f ι π).hom ≫ pullback.snd (π ≫ f) ι) := by
      rw [pullbackRightPullbackFstIso_hom_snd]; infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp this

  have h2 : IsProper (pullback.snd (j ≫ q) ι) := by
    have : (pullback.congrHom hcomm rfl).hom ≫ pullback.snd (π ≫ f) ι = pullback.snd (j ≫ q) ι := by
      rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
    rw [← this]; infer_instance
  have h3 : j₀ ι j q ≫ pullback.snd q ι =
      (pullbackRightPullbackFstIso q ι j).hom ≫ pullback.snd (j ≫ q) ι := by
    rw [pullbackRightPullbackFstIso_hom_snd]
  rw [h3]; infer_instance

include hcomm in
lemma isProper_j₀ : IsProper (j₀ ι j q) :=
  haveI := isProper_j₀_comp f ι π j q hcomm
  IsProper.of_comp (j₀ ι j q) (pullback.snd q ι)

lemma isClopen_range_j₀ (hp : IsProper (j₀ ι j q)) : IsClopen (Set.range (j₀ ι j q)) := by
  refine ⟨?_, ?_⟩
  · haveI := hp; exact (j₀ ι j q).isClosedMap.isClosed_range
  · rw [Scheme.Pullback.range_snd]
    exact (IsOpenImmersion.isOpen_range j).preimage (pP ι q).continuous

variable (V : Set P) (hV : IsClopen V) (hVfib : pP ι q ⁻¹' V = Set.range (j₀ ι j q))
include f ι π j q hcomm V hV hVfib

lemma subset_range_j : V ⊆ Set.range j := by
  intro v hv
  by_contra hvj
  have hW : IsClosed (V ∩ (Set.range j)ᶜ) :=
    hV.1.inter (IsOpenImmersion.isOpen_range j).isClosed_compl
  obtain ⟨w', ⟨hw'V, hw'j⟩, hqw'⟩ := exists_mem_of_isClosed ι q hW ⟨hv, hvj⟩

  have hw'range : w' ∈ Set.range (pP ι q) := by
    rw [Scheme.Pullback.range_fst]; exact hqw'
  obtain ⟨y, rfl⟩ := hw'range
  have hy : y ∈ pP ι q ⁻¹' V := hw'V
  rw [hVfib, Scheme.Pullback.range_snd] at hy
  exact hw'j hy

def Zop : X'.Opens := ⟨j ⁻¹' V, hV.2.preimage j.continuous⟩

lemma isClosed_Zop : IsClosed (Zop j V hV : Set X') := hV.1.preimage j.continuous

lemma image_Zop : j '' (Zop j V hV : Set X') = V :=
  Set.image_preimage_eq_of_subset (subset_range_j f ι π j q hcomm V hV hVfib)

lemma isProper_Zop : IsProper ((Zop j V hV).ι ≫ j ≫ q) := by
  have hrange : Set.range ((Zop j V hV).ι ≫ j) = V := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    exact image_Zop f ι π j q hcomm V hV hVfib
  haveI : IsClosedImmersion ((Zop j V hV).ι ≫ j) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [hrange]; exact hV.1)
  rw [← Category.assoc]; infer_instance

lemma mem_Zop_of {z : X'} (hz : (π ≫ f) z ∈ Set.range ι) : z ∈ (Zop j V hV : Set X') := by
  change j z ∈ V
  have hjz : j z ∈ Set.range (pP ι q) := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, ← Scheme.Hom.comp_apply, hcomm]; exact hz
  obtain ⟨y, hy⟩ := hjz
  have : y ∈ pP ι q ⁻¹' V := by
    rw [hVfib, Scheme.Pullback.range_snd]; exact ⟨z, hy.symm⟩
  rw [← hy]; exact this

lemma isClosed_image_j {C : Set X'} (hC : IsClosed C) (hCZ : C ⊆ (Zop j V hV : Set X')) :
    IsClosed (j '' C) := by
  have heq : j '' C = V ∩ (j '' Cᶜ)ᶜ := by
    ext c
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨hCZ hz, ?_⟩
      rintro ⟨z', hz', hzz'⟩
      exact hz' (j.isOpenEmbedding.injective hzz' ▸ hz)
    · rintro ⟨hcV, hc⟩
      obtain ⟨z, rfl⟩ := subset_range_j f ι π j q hcomm V hV hVfib hcV
      refine ⟨z, ?_, rfl⟩
      by_contra hz
      exact hc ⟨z, hz, rfl⟩
  rw [heq]
  exact hV.1.inter (j.isOpenEmbedding.isOpenMap _ hC.isOpen_compl).isClosed_compl

lemma disjoint_images :
    Disjoint (π '' (Zop j V hV : Set X')) (π '' (Zop j V hV : Set X')ᶜ) := by
  rw [Set.disjoint_left]
  rintro x ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, hx⟩

  have hC1Z : closure {z₁} ⊆ (Zop j V hV : Set X') :=
    (isClosed_Zop f ι π j q hcomm V hV hVfib).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hz₁)
  have hcl : IsClosed (j '' closure {z₁}) := isClosed_image_j f ι π j q hcomm V hV hVfib isClosed_closure hC1Z
  obtain ⟨w, ⟨z₁', hz₁', rfl⟩, hqw⟩ :=
    exists_mem_of_isClosed ι q hcl ⟨z₁, subset_closure rfl, rfl⟩

  have hc : π z₁' ∈ closure {π z₁} := by
    rw [← Set.image_singleton]
    exact image_closure_subset_closure_image π.continuous ⟨z₁', hz₁', rfl⟩
  have hcs : f (π z₁') ∈ Set.range ι := by
    rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]; exact hqw

  have hsub : closure {π z₁} ⊆ π '' closure {z₂} :=
    (π.isClosedMap _ isClosed_closure).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr ⟨z₂, subset_closure rfl, hx⟩)
  obtain ⟨z₂', hz₂', hzz⟩ := hsub hc

  have hz₂'Z : z₂' ∉ (Zop j V hV : Set X') := by
    have : closure {z₂} ⊆ (Zop j V hV : Set X')ᶜ :=
      (Zop j V hV).isOpen.isClosed_compl.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hz₂)
    exact this hz₂'
  apply hz₂'Z
  apply mem_Zop_of f ι π j q hcomm V hV hVfib
  rw [Scheme.Hom.comp_apply, hzz]; exact hcs

def Uop : X.Opens :=
  ⟨(π '' (Zop j V hV : Set X')ᶜ)ᶜ,
    (π.isClosedMap _ (Zop j V hV).isOpen.isClosed_compl).isOpen_compl⟩

lemma coe_Uop_eq : (Uop π j V hV : Set X) = π '' (Zop j V hV : Set X') := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := π.surjective x
    by_cases hz : z ∈ (Zop j V hV : Set X')
    · exact ⟨z, hz, rfl⟩
    · exact absurd ⟨z, hz, rfl⟩ hx
  · intro hx hx'
    exact Set.disjoint_left.mp (disjoint_images f ι π j q hcomm V hV hVfib) hx hx'

lemma isClosed_Uop : IsClosed (Uop π j V hV : Set X) := by
  rw [coe_Uop_eq f ι π j q hcomm V hV hVfib]
  exact π.isClosedMap _ (isClosed_Zop f ι π j q hcomm V hV hVfib)

lemma range_fst_subset_Uop : Set.range (pullback.fst f ι) ⊆ (Uop π j V hV : Set X) := by
  rintro x hx ⟨z, hz, rfl⟩
  rw [Scheme.Pullback.range_fst] at hx
  exact hz (mem_Zop_of f ι π j q hcomm V hV hVfib (by rw [Scheme.Hom.comp_apply]; exact hx))

noncomputable def πU : (Zop j V hV).toScheme ⟶ (Uop π j V hV).toScheme :=
  IsOpenImmersion.lift (Uop π j V hV).ι ((Zop j V hV).ι ≫ π) (by
    rw [Scheme.Opens.range_ι, coe_Uop_eq f ι π j q hcomm V hV hVfib, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι])

lemma πU_fac : πU f ι π j q hcomm V hV hVfib ≫ (Uop π j V hV).ι = (Zop j V hV).ι ≫ π :=
  IsOpenImmersion.lift_fac _ _ _

lemma surjective_πU : Surjective (πU f ι π j q hcomm V hV hVfib) := by
  refine ⟨fun u => ?_⟩
  have hu : (Uop π j V hV).ι u ∈ (Uop π j V hV : Set X) := by
    rw [← Scheme.Opens.range_ι]; exact ⟨u, rfl⟩
  rw [coe_Uop_eq f ι π j q hcomm V hV hVfib] at hu
  obtain ⟨z, hz, hzu⟩ := hu
  obtain ⟨w, rfl⟩ : z ∈ Set.range (Zop j V hV).ι := by rw [Scheme.Opens.range_ι]; exact hz
  refine ⟨w, (Uop π j V hV).ι.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, πU_fac f ι π j q hcomm V hV hVfib, Scheme.Hom.comp_apply, hzu]

lemma isProper_Uop : IsProper ((Uop π j V hV).ι ≫ f) := by
  have h1 : IsProper (πU f ι π j q hcomm V hV hVfib ≫ (Uop π j V hV).ι ≫ f) := by
    rw [← Category.assoc, πU_fac f ι π j q hcomm V hV hVfib, Category.assoc, ← hcomm]
    exact isProper_Zop f ι π j q hcomm V hV hVfib
  haveI := surjective_πU f ι π j q hcomm V hV hVfib
  have h2 : UniversallyClosed ((Uop π j V hV).ι ≫ f) :=
    UniversallyClosed.of_comp_surjective (πU f ι π j q hcomm V hV hVfib) _
  exact ⟨⟩

end Main

end ProperClopenNbhd

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A))
    [IsClosedImmersion ι] [IsProper (pullback.snd f ι)] :
    ∃ U : X.Opens, IsClosed (U : Set X) ∧ IsProper (U.ι ≫ f) ∧
      Set.range (pullback.fst f ι) ⊆ (U : Set X) := by
  obtain ⟨X', P, π, j, q, hπ, hπs, hj, hq, hcomm⟩ :=
    AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated f
  have hp := ProperClopenNbhd.isProper_j₀ f ι π j q hcomm
  obtain ⟨V, hV, hVfib⟩ :=
    AlgebraicGeometry.exists_isClopen_preimage_eq_of_isProper_of_isAdicComplete q ι
      (Set.range (ProperClopenNbhd.j₀ ι j q)) (ProperClopenNbhd.isClopen_range_j₀ ι j q hp)
  exact ⟨ProperClopenNbhd.Uop π j V hV, ProperClopenNbhd.isClosed_Uop f ι π j q hcomm V hV hVfib,
    ProperClopenNbhd.isProper_Uop f ι π j q hcomm V hV hVfib,
    ProperClopenNbhd.range_fst_subset_Uop f ι π j q hcomm V hV hVfib⟩

end S_AlgebraicGeometry_exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete (solution)
