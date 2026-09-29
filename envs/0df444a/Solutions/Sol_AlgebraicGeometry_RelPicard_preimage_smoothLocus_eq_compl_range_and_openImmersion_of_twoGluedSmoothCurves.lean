-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9b3d3f5f-a8db-57a9-83bf-5d845d6698c8

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_isOpen_isIrreducible_nhd
import Theorems.Thm_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_opensRestrict_pullback_snd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [Flat c] [LocallyOfFinitePresentation c]
    (U : C.Opens) [Smooth (U.ι ≫ c)] (hUmax : ∀ W : C.Opens, Smooth (W.ι ≫ c) → W ≤ U)
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hXred : IsReduced (pullback c s))
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (pullback.snd c s)) (i₂ : SchemeHomOver c₂ (pullback.snd c s))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : ↥(pullback c s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hne₁ : ¬ Set.range i₁.1.base ⊆ Set.range i₂.1.base) (hne₂ : ¬ Set.range i₂.1.base ⊆ Set.range i₁.1.base)
    (p : ↥(pullback c s)) (hp : p ∈ Set.range i₁.1.base)
    (hpU : p ∈ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))) :
    ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
      (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
    Set.range i₁.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
      connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) p ∧
    Set.range i₂.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
      ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) p ∧
    (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.1.base)ᶜ ∧
      IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
    (∃ W₂ : (pullback c s).Opens, (W₂ : Set ↥(pullback c s)) = (Set.range i₁.1.base)ᶜ ∧
      IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)) := by
  classical

  set T : Set ↥(pullback c s) := ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) with hTdef
  set Z₁ : Set ↥(pullback c s) := Set.range i₁.1.base with hZ₁
  set Z₂ : Set ↥(pullback c s) := Set.range i₂.1.base with hZ₂
  have hZ₁c : IsClosed Z₁ := i₁.1.isClosedEmbedding.isClosed_range
  have hZ₂c : IsClosed Z₂ := i₂.1.isClosedEmbedding.isClosed_range
  have hcov : ∀ z : ↥(pullback c s), z ∈ Z₁ ∪ Z₂ := fun z => hjs z
  haveI : IsReduced (pullback c s) := hXred

  have hN : Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base = Z₁ ∩ Z₂ := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨⟨(pullback.fst i₁.1 i₂.1).base w, rfl⟩, ⟨(pullback.snd i₁.1 i₂.1).base w, ?_⟩⟩
      change ((pullback.snd i₁.1 i₂.1) ≫ i₂.1).base w = ((pullback.fst i₁.1 i₂.1) ≫ i₁.1).base w
      rw [pullback.condition]
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback a b (ha.trans hb.symm)
      exact ⟨w, by rw [Scheme.Hom.comp_apply, hw, ha]⟩

  have hoi : ∀ {D D' : Scheme.{u}} (d : D ⟶ Spec (CommRingCat.of k)) (d' : D' ⟶ Spec (CommRingCat.of k))
      [SmoothOfRelativeDimension 1 d]
      (j : SchemeHomOver d (pullback.snd c s)) (j' : SchemeHomOver d' (pullback.snd c s))
      [IsClosedImmersion j.1] [IsClosedImmersion j'.1],
      (∀ z : ↥(pullback c s), z ∈ Set.range j.1.base ∨ z ∈ Set.range j'.1.base) →
      ∃ W : (pullback c s).Opens, (W : Set ↥(pullback c s)) = (Set.range j'.1.base)ᶜ ∧
        IsOpenImmersion ((j.1 ⁻¹ᵁ W).ι ≫ j.1) ∧ SmoothOfRelativeDimension 1 (W.ι ≫ pullback.snd c s) := by
    intro D D' d d' _ j j' _ _ hjj'
    let W : (pullback c s).Opens := ⟨(Set.range j'.1.base)ᶜ, j'.1.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    refine ⟨W, rfl, ?_⟩

    haveI : Surjective (j.1 ∣_ W) := ⟨fun ⟨z, hz⟩ => by
      rcases hjj' z with ⟨a, rfl⟩ | h
      · exact ⟨⟨a, hz⟩, Subtype.ext (morphismRestrict_base_coe j.1 W ⟨a, hz⟩)⟩
      · exact absurd h hz⟩
    haveI : IsIso (j.1 ∣_ W) := isIso_of_isClosedImmersion_of_surjective _
    have hfac : (j.1 ⁻¹ᵁ W).ι ≫ j.1 = (j.1 ∣_ W) ≫ W.ι := (morphismRestrict_ι j.1 W).symm
    refine ⟨by rw [hfac]; infer_instance, ?_⟩

    have hj2 : j.1 ≫ pullback.snd c s = d := j.2
    have hW : W.ι ≫ pullback.snd c s = inv (j.1 ∣_ W) ≫ ((j.1 ⁻¹ᵁ W).ι ≫ d) := by
      symm
      calc inv (j.1 ∣_ W) ≫ ((j.1 ⁻¹ᵁ W).ι ≫ d)
          = inv (j.1 ∣_ W) ≫ (((j.1 ⁻¹ᵁ W).ι ≫ j.1) ≫ pullback.snd c s) := by rw [Category.assoc, hj2]
        _ = inv (j.1 ∣_ W) ≫ (((j.1 ∣_ W) ≫ W.ι) ≫ pullback.snd c s) := by rw [hfac]
        _ = W.ι ≫ pullback.snd c s := by simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [hW]
    haveI : SmoothOfRelativeDimension (0 + 1) ((j.1 ⁻¹ᵁ W).ι ≫ d) := inferInstance
    haveI : SmoothOfRelativeDimension 1 ((j.1 ⁻¹ᵁ W).ι ≫ d) := by simpa using this
    exact MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  obtain ⟨W₁, hW₁, hW₁oi, hW₁sm⟩ := hoi c₁ c₂ i₁ i₂ hjs
  obtain ⟨W₂, hW₂, hW₂oi, hW₂sm⟩ := hoi c₂ c₁ i₂ i₁ (fun z => (hjs z).symm)

  have hoff : ∀ (W : (pullback c s).Opens), SmoothOfRelativeDimension 1 (W.ι ≫ pullback.snd c s) →
      (W : Set ↥(pullback c s)) ⊆ T := by
    intro W hW z hz
    obtain ⟨V, hV, hVsm⟩ :=
      AlgebraicGeometry.exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_opensRestrict_pullback_snd
        c s W hW ((pullback.fst c s).base z) ⟨z, hz, rfl⟩
    haveI := hVsm
    have hle : V ≤ U := hUmax V inferInstance
    exact hle hV
  have hsup : Tᶜ ⊆ Z₁ ∩ Z₂ := by
    intro z hz
    by_contra hnot
    apply hz
    rcases hcov z with h1 | h2
    · have : z ∈ (W₁ : Set ↥(pullback c s)) := by
        rw [hW₁]; exact fun h2 => hnot ⟨h1, h2⟩
      exact hoff W₁ hW₁sm this
    · have : z ∈ (W₂ : Set ↥(pullback c s)) := by
        rw [hW₂]; exact fun h1 => hnot ⟨h1, h2⟩
      exact hoff W₂ hW₂sm this

  have hsq : IsPullback ((pullback.fst c s) ∣_ U) (pullback.fst c s ⁻¹ᵁ U).ι U.ι (pullback.fst c s) :=
    isPullback_morphismRestrict _ _
  have hbig : IsPullback ((pullback.fst c s) ∣_ U) ((pullback.fst c s ⁻¹ᵁ U).ι ≫ pullback.snd c s) (U.ι ≫ c) s :=
    hsq.paste_vert (IsPullback.of_hasPullback c s)
  haveI hTsm : Smooth ((pullback.fst c s ⁻¹ᵁ U).ι ≫ pullback.snd c s) :=
    MorphismProperty.of_isPullback hbig inferInstance

  haveI : IsIntegral C₁ := GeometricallyIntegral.isIntegral_of_subsingleton c₁
  haveI : IsIntegral C₂ := GeometricallyIntegral.isIntegral_of_subsingleton c₂
  have hZ₁irr : IsIrreducible Z₁ := by
    rw [hZ₁, ← Set.image_univ]; exact IsIrreducible.image (IrreducibleSpace.isIrreducible_univ _) _ i₁.1.base.hom.continuous.continuousOn
  have hZ₂irr : IsIrreducible Z₂ := by
    rw [hZ₂, ← Set.image_univ]; exact IsIrreducible.image (IrreducibleSpace.isIrreducible_univ _) _ i₂.1.base.hom.continuous.continuousOn
  have hsub : T ⊆ (Z₁ ∩ Z₂)ᶜ := by
    rintro z hzT ⟨hz1, hz2⟩

    obtain ⟨Ω, hzΩ, hΩirr⟩ := AlgebraicGeometry.Smooth.exists_isOpen_isIrreducible_nhd
      ((pullback.fst c s ⁻¹ᵁ U).ι ≫ pullback.snd c s) ⟨z, hzT⟩
    let Ω' : Set ↥(pullback c s) := (pullback.fst c s ⁻¹ᵁ U).ι.base '' (Ω : Set ↥((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Scheme.{u}))
    have hΩ'irr : IsIrreducible Ω' := hΩirr.image _ (pullback.fst c s ⁻¹ᵁ U).ι.base.hom.continuous.continuousOn
    have hΩ'open : IsOpen Ω' := (pullback.fst c s ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap _ Ω.2
    have hzΩ' : z ∈ Ω' := ⟨⟨z, hzT⟩, hzΩ, rfl⟩
    have hΩ'cov : Ω' ⊆ Z₁ ∪ Z₂ := fun w _ => hcov w
    rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hΩ'irr.2) Z₁ Z₂ hZ₁c hZ₂c hΩ'cov with h | h
    ·
      apply hne₂
      calc Z₂ ⊆ closure (Z₂ ∩ Ω') := subset_closure_inter_of_isPreirreducible_of_isOpen hZ₂irr.2 hΩ'open ⟨z, hz2, hzΩ'⟩
        _ ⊆ Z₁ := closure_minimal (fun w hw => h hw.2) hZ₁c
    · apply hne₁
      calc Z₁ ⊆ closure (Z₁ ∩ Ω') := subset_closure_inter_of_isPreirreducible_of_isOpen hZ₁irr.2 hΩ'open ⟨z, hz1, hzΩ'⟩
        _ ⊆ Z₂ := closure_minimal (fun w hw => h hw.2) hZ₂c
  have hT : T = (Z₁ ∩ Z₂)ᶜ := Set.Subset.antisymm hsub (Set.compl_subset_comm.mp hsup)

  have hA : Z₁ ∩ T = T ∩ Z₂ᶜ := by
    ext w; constructor
    · rintro ⟨h1, hT'⟩; exact ⟨hT', fun h2 => (hT ▸ hT' : w ∈ (Z₁ ∩ Z₂)ᶜ) ⟨h1, h2⟩⟩
    · rintro ⟨hT', h2⟩; exact ⟨(hcov w).resolve_right h2, hT'⟩
  have hB : Z₂ ∩ T = T ∩ Z₁ᶜ := by
    ext w; constructor
    · rintro ⟨h2, hT'⟩; exact ⟨hT', fun h1 => (hT ▸ hT' : w ∈ (Z₁ ∩ Z₂)ᶜ) ⟨h1, h2⟩⟩
    · rintro ⟨hT', h1⟩; exact ⟨(hcov w).resolve_left h1, hT'⟩
  have hTopen : IsOpen T := (pullback.fst c s ⁻¹ᵁ U).2
  have hAopen : IsOpen (Z₁ ∩ T) := by rw [hA]; exact hTopen.inter hZ₂c.isOpen_compl
  have hBopen : IsOpen (Z₂ ∩ T) := by rw [hB]; exact hTopen.inter hZ₁c.isOpen_compl
  have hpA : p ∈ Z₁ ∩ T := ⟨hp, hpU⟩

  have hAirr : IsPreirreducible (Z₁ ∩ T) := hZ₁irr.2.open_subset hAopen Set.inter_subset_left
  have hdisj : Disjoint (Z₁ ∩ T) (Z₂ ∩ T) := by
    rw [Set.disjoint_left]
    rintro w ⟨h1, hT'⟩ ⟨h2, -⟩
    exact (hT ▸ hT' : w ∈ (Z₁ ∩ Z₂)ᶜ) ⟨h1, h2⟩
  have hcc : connectedComponentIn T p = Z₁ ∩ T := by
    refine Set.Subset.antisymm ?_ (hAirr.isPreconnected.subset_connectedComponentIn hpA Set.inter_subset_right)
    have hccT : connectedComponentIn T p ⊆ (Z₁ ∩ T) ∪ (Z₂ ∩ T) := fun w hw => by
      have hwT := connectedComponentIn_subset T p hw
      rcases hcov w with h1 | h2
      · exact Or.inl ⟨h1, hwT⟩
      · exact Or.inr ⟨h2, hwT⟩
    rcases isPreconnected_connectedComponentIn.subset_or_subset hAopen hBopen hdisj hccT with h | h
    · exact h
    · exfalso
      have hpcc : p ∈ connectedComponentIn T p := mem_connectedComponentIn hpU
      exact Set.disjoint_left.mp hdisj hpA (h hpcc)

  refine ⟨?_, ?_, ?_, ⟨W₁, hW₁, hW₁oi⟩, ⟨W₂, hW₂, hW₂oi⟩⟩
  · rw [hN]; exact hT
  · rw [hcc]
  · rw [hcc]
    ext w
    constructor
    · rintro ⟨h2, hT'⟩
      exact ⟨hT', fun hA' => Set.disjoint_left.mp hdisj hA' ⟨h2, hT'⟩⟩
    · rintro ⟨hT', hnA⟩
      exact ⟨(hcov w).resolve_left fun h1 => hnA ⟨h1, hT'⟩, hT'⟩

end S_AlgebraicGeometry_RelPicard_preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves (solution)
