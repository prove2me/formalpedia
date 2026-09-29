-- Prove2me | solution 1 for AlgebraicGeometry.mem_smoothLocus_of_not_mem_range_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a35c61e9-c827-5494-a9ba-1030debf4adc

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_opensRestrict_pullback_snd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_mem_smoothLocus_of_not_mem_range_of_isClosedImmersion
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_mem_smoothLocus_of_not_mem_range_of_isClosedImmersion.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension.smooth IsClosedImmersion.isIso_iff_ker_eq_bot Surjective SmoothOfRelativeDimension Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal Scheme.Hom IsClosedImmersion.isClosedEmbedding Scheme.Hom.support_ker Spec Scheme Smooth Flat HasRingHomProperty.comp_of_isOpenImmersion Scheme.IdealSheafData.vanishingIdeal_top IsClosedImmersion IsReduced Scheme.nilradical_eq_bot LocallyOfFinitePresentation isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback HasRingHomProperty range_eq_univ Scheme.IdealSheafData exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_opensRestrict_pullback_snd"
p2m_open "AlgebraicGeometry"

theorem isIso_of_isClosedImmersion_of_surjective_of_isReduced {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [IsClosedImmersion f] [IsReduced Y] (hf : Function.Surjective f.base) : IsIso f := by
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot, ← le_bot_iff, ← Scheme.nilradical_eq_bot (X := Y),
    ← Scheme.IdealSheafData.vanishingIdeal_top, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]

  have h : ((f.ker).support : Set Y) = Set.univ := by
    rw [Scheme.Hom.support_ker, Set.range_eq_univ.mpr hf, closure_univ]
  intro z _
  show z ∈ ((f.ker).support : Set Y)
  rw [h]; trivial

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "IdealSheafData.le_support_iff_le_vanishingIdeal Hom Hom.support_ker IdealSheafData.vanishingIdeal_top nilradical_eq_bot nilradical Opens Pullback.exists_preimage_pullback IdealSheafData" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "image preimage_smoothLocus_eq smoothLocus surjective support_ker smoothLocus_eq_top ker isClosedEmbedding" end Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.le_smoothLocus_of_smoothOfRelativeDimension' {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (n : ℕ) (U : X.Opens) [SmoothOfRelativeDimension n (U.ι ≫ f)] :
    U ≤ f.smoothLocus := by
  haveI : Smooth (U.ι ≫ f) := SmoothOfRelativeDimension.smooth n _
  intro x hx
  have h : (Opens.map U.ι.base).obj f.smoothLocus = ⊤ := by
    rw [preimage_smoothLocus_eq U.ι f, smoothLocus_eq_top]
  have hx' : (⟨x, hx⟩ : U) ∈ (Opens.map U.ι.base).obj f.smoothLocus := by
    rw [h]; exact Opens.mem_top _
  exact hx'

theorem mem_smoothLocus_of_not_mem_range_of_isClosedImmersion
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [Flat c] [LocallyOfFinitePresentation c]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    [IsReduced (pullback c x)]
    {M₁ M₂ : Scheme.{u}} (g₁ : M₁ ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 g₁]
    (i₁ : M₁ ⟶ pullback c x) (i₂ : M₂ ⟶ pullback c x) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (h₁ : i₁ ≫ pullback.snd c x = g₁)
    (hcover : ∀ z : ↥(pullback c x), z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (y : ↥(pullback c x)) (hy : y ∉ Set.range i₂.base) :
    (pullback.fst c x).base y ∈ c.smoothLocus := by

  let Ω : (pullback c x).Opens :=
    ⟨(Set.range i₂.base)ᶜ, (IsClosedImmersion.isClosedEmbedding i₂).isClosed_range.isOpen_compl⟩
  have hyΩ : y ∈ Ω := hy

  haveI : IsReduced (Ω : Scheme.{u}) := isReduced_of_isOpenImmersion Ω.ι
  have hf : Function.Surjective (pullback.snd i₁ Ω.ι).base := by
    intro z
    have hz : Ω.ι.base z ∈ Set.range i₁.base := by
      rcases hcover (Ω.ι.base z) with h | h
      · exact h
      · exact absurd h z.2
    obtain ⟨m, hm⟩ := hz
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback m z hm
    exact ⟨w, hw⟩
  haveI : IsIso (pullback.snd i₁ Ω.ι) :=
    isIso_of_isClosedImmersion_of_surjective_of_isReduced (pullback.snd i₁ Ω.ι) hf

  have hΩ : SmoothOfRelativeDimension 1 (Ω.ι ≫ pullback.snd c x) := by
    have e : Ω.ι ≫ pullback.snd c x = inv (pullback.snd i₁ Ω.ι) ≫ pullback.fst i₁ Ω.ι ≫ g₁ := by
      rw [← h₁, pullback.condition_assoc, IsIso.inv_hom_id_assoc]
    rw [e]
    have h1 : SmoothOfRelativeDimension 1 (pullback.fst i₁ Ω.ι ≫ g₁) :=
      HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension 1) (f := pullback.fst i₁ Ω.ι) g₁ ‹_›
    exact HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension 1)
      (f := inv (pullback.snd i₁ Ω.ι)) (pullback.fst i₁ Ω.ι ≫ g₁) h1

  obtain ⟨W, hyW, hW⟩ :=
    AlgebraicGeometry.exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_opensRestrict_pullback_snd
      c x Ω hΩ ((pullback.fst c x).base y) ⟨y, hyΩ, rfl⟩
  haveI := hW
  exact Scheme.Hom.le_smoothLocus_of_smoothOfRelativeDimension' c 1 W hyW

end AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_mem_smoothLocus_of_not_mem_range_of_isClosedImmersion.AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [Flat c] [LocallyOfFinitePresentation c]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    [IsReduced (pullback c x)]
    {M₁ M₂ : Scheme.{u}} (g₁ : M₁ ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 g₁]
    (i₁ : M₁ ⟶ pullback c x) (i₂ : M₂ ⟶ pullback c x) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (h₁ : i₁ ≫ pullback.snd c x = g₁)
    (hcover : ∀ z : ↥(pullback c x), z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (y : ↥(pullback c x)) (hy : y ∉ Set.range i₂.base) :
    (pullback.fst c x).base y ∈ c.smoothLocus :=
  AlgebraicGeometry.mem_smoothLocus_of_not_mem_range_of_isClosedImmersion c x g₁ i₁ i₂ h₁ hcover y hy

end S_AlgebraicGeometry_mem_smoothLocus_of_not_mem_range_of_isClosedImmersion
end P2MW
export P2MW.S_AlgebraicGeometry_mem_smoothLocus_of_not_mem_range_of_isClosedImmersion (solution)
