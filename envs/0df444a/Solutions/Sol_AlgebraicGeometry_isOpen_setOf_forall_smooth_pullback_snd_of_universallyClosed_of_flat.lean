-- Prove2me | solution 1 for AlgebraicGeometry.isOpen_setOf_forall_smooth_pullback_snd_of_universallyClosed_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3bcd8a98-1d72-55a6-b634-0bebb36bd941

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isOpen_setOf_forall_preimage_mem_of_universallyClosed
import Theorems.Thm_AlgebraicGeometry_Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isOpen_setOf_forall_smooth_pullback_snd_of_universallyClosed_of_flat
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace H2a1

theorem smoothLocus_comp_of_isOpenImmersion {X U Y : Scheme.{u}} (g : X ⟶ U) (i : U ⟶ Y) [IsOpenImmersion i]
    [LocallyOfFinitePresentation g] : (g ≫ i).smoothLocus = g.smoothLocus := by
  ext x
  show x ∈ (g ≫ i).smoothLocus ↔ x ∈ g.smoothLocus
  simp only [Scheme.Hom.mem_smoothLocus]
  rw [Scheme.Hom.stalkMap_comp]
  change ((g.stalkMap x).hom.comp (i.stalkMap (g.base x)).hom).FormallySmooth ↔ (g.stalkMap x).hom.FormallySmooth
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso (i.stalkMap (g.base x)) (g.stalkMap x)

variable {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))

theorem smooth_morphismRestrict_of_forall_mem_smoothLocus [LocallyOfFinitePresentation f]
    (V : (Spec (CommRingCat.of S)).Opens) (hV : ∀ z : Z, f.base z ∈ (V : Set _) → z ∈ f.smoothLocus) :
    Smooth (f ∣_ V) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  intro z _
  rw [← smoothLocus_comp_of_isOpenImmersion (f ∣_ V) V.ι, Scheme.Hom.mem_smoothLocus, morphismRestrict_ι]
  have hz : (f ⁻¹ᵁ V).ι.base z ∈ f.smoothLocus := hV _ (by rw [Scheme.Opens.ι_apply]; exact z.2)
  exact (Scheme.Hom.mem_smoothLocus.mp ((Scheme.Hom.preimage_smoothLocus_eq (f ⁻¹ᵁ V).ι f).le hz))

theorem smooth_pullback_snd_of_smooth_morphismRestrict (V : (Spec (CommRingCat.of S)).Opens) [Smooth (f ∣_ V)]
    {k : Type u} [Field k] (x : S →+* k) (hx : (⟨RingHom.ker x, RingHom.ker_isPrime x⟩ : PrimeSpectrum S) ∈ V) :
    Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) := by

  have hrange : Set.range (Spec.map (CommRingCat.ofHom x)).base ⊆ Set.range V.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hp : (Spec.map (CommRingCat.ofHom x)).base p = (⟨RingHom.ker x, RingHom.ker_isPrime x⟩ : PrimeSpectrum S) := by
      apply PrimeSpectrum.ext
      show (PrimeSpectrum.comap (CommRingCat.ofHom x).hom p).asIdeal = RingHom.ker x
      rw [PrimeSpectrum.comap_asIdeal, Ideal.eq_bot_of_prime p.asIdeal, ← RingHom.ker_eq_comap_bot]
      rfl
    rw [hp]; exact hx
  let y := IsOpenImmersion.lift V.ι (Spec.map (CommRingCat.ofHom x)) hrange
  have hy : y ≫ V.ι = Spec.map (CommRingCat.ofHom x) := IsOpenImmersion.lift_fac _ _ _

  have houter : IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom x))) (pullback.snd f (Spec.map (CommRingCat.ofHom x)))
      f (y ≫ V.ι) := by
    rw [hy]; exact IsPullback.of_hasPullback _ _
  have hl : Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom x))).base ⊆ Set.range (f ⁻¹ᵁ V).ι.base := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    show f.base ((pullback.fst f (Spec.map (CommRingCat.ofHom x))).base q) ∈ V
    have hc := congrArg (fun φ => φ.base q) (pullback.condition (f := f) (g := Spec.map (CommRingCat.ofHom x)))
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hc
    change f.base ((pullback.fst f (Spec.map (CommRingCat.ofHom x))).base q) ∈ V
    rw [hc]
    have hmem := hrange ⟨(pullback.snd f (Spec.map (CommRingCat.ofHom x))).base q, rfl⟩
    rwa [Scheme.Opens.range_ι] at hmem
  let t := IsOpenImmersion.lift (f ⁻¹ᵁ V).ι (pullback.fst f (Spec.map (CommRingCat.ofHom x))) hl
  have ht : t ≫ (f ⁻¹ᵁ V).ι = pullback.fst f (Spec.map (CommRingCat.ofHom x)) := IsOpenImmersion.lift_fac _ _ _
  have hsq : IsPullback t (pullback.snd f (Spec.map (CommRingCat.ofHom x))) (f ∣_ V) y := by
    refine IsPullback.of_right (by rw [ht]; exact houter) ?_ (isPullback_morphismRestrict f V).flip

    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc, ht, hy, pullback.condition]
  exact MorphismProperty.of_isPullback (P := @Smooth) hsq inferInstance

theorem mem_smoothLocus_of_smooth_geometricFibre [LocallyOfFinitePresentation f] [Flat f] (z : Z)
    (hs : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k), RingHom.ker x = (f.base z).asIdeal →
      Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x)))) :
    z ∈ f.smoothLocus := by
  set s := f.base z with hs_def
  let κ : Type u := ↑((Spec (CommRingCat.of S)).residueField s)
  let kb : Type u := AlgebraicClosure κ
  let h : Spec (CommRingCat.of kb) ⟶ Spec ((Spec (CommRingCat.of S)).residueField s) :=
    Spec.map (CommRingCat.ofHom (algebraMap κ kb))
  let h₀ := h ≫ (Spec (CommRingCat.of S)).fromSpecResidueField s
  obtain ⟨φ, hφ⟩ := Spec.map_surjective h₀

  have hker : RingHom.ker φ.hom = s.asIdeal := by
    have h1 : (Spec.map φ).base (IsLocalRing.closedPoint kb) = s := by
      rw [hφ]
      show ((Spec (CommRingCat.of S)).fromSpecResidueField s).base (h.base _) = s
      exact Scheme.fromSpecResidueField_apply _ _
    rw [Spec.map_apply] at h1
    have h2 : Ideal.comap φ.hom (IsLocalRing.closedPoint kb).asIdeal = s.asIdeal := by
      rw [← PrimeSpectrum.comap_asIdeal]; exact congrArg PrimeSpectrum.asIdeal h1
    rwa [Ideal.eq_bot_of_prime (IsLocalRing.closedPoint kb).asIdeal, ← RingHom.ker_eq_comap_bot] at h2
  have hsm : Smooth (pullback.snd f h₀) := by
    rw [← hφ]; have := hs kb φ.hom hker; rwa [CommRingCat.ofHom_hom] at this

  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) h := by
    refine ⟨⟨?_, ?_⟩, inferInstance⟩
    · exact ⟨fun p => ⟨IsLocalRing.closedPoint kb, Subsingleton.elim _ _⟩⟩
    · rw [Flat.SpecMap_iff]
      show (algebraMap κ kb).Flat
      exact RingHom.flat_algebraMap_iff.mpr inferInstance

  have houter : IsPullback (pullback.fst f h₀) (pullback.snd f h₀) f (h ≫ (Spec (CommRingCat.of S)).fromSpecResidueField s) :=
    IsPullback.of_hasPullback _ _
  let t : pullback f h₀ ⟶ f.fiber s := pullback.lift (pullback.fst f h₀) (pullback.snd f h₀ ≫ h)
    (by rw [pullback.condition, Category.assoc])
  have ht : t ≫ pullback.fst f ((Spec (CommRingCat.of S)).fromSpecResidueField s) = pullback.fst f h₀ := pullback.lift_fst _ _ _
  have hsq : IsPullback t (pullback.snd f h₀) (f.fiberToSpecResidueField s) h := by
    refine IsPullback.of_right (by rw [ht]; exact houter) ?_ (IsPullback.of_hasPullback f ((Spec (CommRingCat.of S)).fromSpecResidueField s))
    exact pullback.lift_snd _ _ _
  haveI : Smooth (f.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq.flip hQ hsm

  have hz : (f.fiberι s).base (f.asFiber z) = z := f.fiberι_asFiber z
  rw [← hz]
  refine Scheme.Hom.fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField f s _ ?_
  rw [Scheme.Hom.smoothLocus_eq_top]; trivial

theorem main {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    [UniversallyClosed f] [Flat f] [LocallyOfFinitePresentation f] :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x)))} ∧
    ∀ V : (Spec (CommRingCat.of S)).Opens,
      (V : Set ↥(Spec (CommRingCat.of S))) ⊆ {s | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x)))} →
      Smooth (f ∣_ V) := by
  have hopen : IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ z : Z, f.base z = s → z ∈ f.smoothLocus} := by
    simpa using AlgebraicGeometry.isOpen_setOf_forall_preimage_mem_of_universallyClosed f (𝟙 Z) f.smoothLocus
  have key : {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x)))} =
      {s | ∀ z : Z, f.base z = s → z ∈ f.smoothLocus} := by
    ext s
    constructor
    · intro hs z hz
      subst hz
      exact mem_smoothLocus_of_smooth_geometricFibre f z hs
    · intro hs k _ _ x hx

      let W : (Spec (CommRingCat.of S)).Opens := ⟨{s | ∀ z : Z, f.base z = s → z ∈ f.smoothLocus}, hopen⟩
      haveI : Smooth (f ∣_ W) := smooth_morphismRestrict_of_forall_mem_smoothLocus f W (fun z hz => hz z rfl)
      refine smooth_pullback_snd_of_smooth_morphismRestrict f W x ?_
      have : (⟨RingHom.ker x, RingHom.ker_isPrime x⟩ : PrimeSpectrum S) = s := PrimeSpectrum.ext hx
      rw [this]; exact hs
  refine ⟨?_, fun V hV => ?_⟩
  · rw [key]; exact hopen
  · rw [key] at hV
    exact smooth_morphismRestrict_of_forall_mem_smoothLocus f V (fun z hz => hV hz z rfl)

end H2a1

theorem solution
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    [UniversallyClosed f] [Flat f] [LocallyOfFinitePresentation f] :
    IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x)))} ∧
    ∀ V : (Spec (CommRingCat.of S)).Opens,
      (V : Set ↥(Spec (CommRingCat.of S))) ⊆ {s | ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
        RingHom.ker x = s.asIdeal → Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x)))} →
      Smooth (f ∣_ V) :=
  H2a1.main f

end S_AlgebraicGeometry_isOpen_setOf_forall_smooth_pullback_snd_of_universallyClosed_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_isOpen_setOf_forall_smooth_pullback_snd_of_universallyClosed_of_flat (solution)
