-- Prove2me | solution 1 for AlgebraicGeometry.exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/04cd740c-2516-59b7-8664-14df1e0fad21

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Theorems.Thm_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed.AlgebraicGeometry.RelPicard NeronModelInfra"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension.smooth Surjective SmoothOfRelativeDimension IsProper Scheme.Hom GeometricallyIntegral GeometricallyIrreducible pullbackRestrictIsoRestrict_inv_fst Scheme.homeoOfIso LocallyOfFiniteType Spec Spec.map Scheme Smooth IsOpenImmersion Scheme.Pullback.range_snd IsClosedImmersion IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Scheme.isoOfEq_hom_ι_assoc Scheme.Pullback.range_fst_comp GeometricallyIrreducible.irreducibleSpace_of_subsingleton Scheme.Hom.comp_preimage isReduced_of_isOpenImmersion Scheme.isoOfEq geometrically isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "sectionFibrePoint"
namespace T2Transport
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem coe_preimage_opens {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens) :
    ((f ⁻¹ᵁ W : X.Opens) : Set ↥X) = f.base ⁻¹' (W : Set ↥Y) := rfl

scoped instance subsingleton_spec_field (K : Type u) [Field K] : Subsingleton ↥(Spec (CommRingCat.of K)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum K))

scoped instance nonempty_spec_field (K : Type u) [Field K] : Nonempty ↥(Spec (CommRingCat.of K)) :=
  ⟨IsLocalRing.closedPoint K⟩

end AlgebraicGeometry.RelPicard.T2Transport
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed.AlgebraicGeometry.RelPicard.T2Transport"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed.AlgebraicGeometry"

open AlgebraicGeometry.RelPicard.T2Transport in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (U : C.Opens) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {k₀ : Type u} [Field k₀] [IsAlgClosed k₀] (s₀ : Spec (CommRingCat.of k₀) ⟶ Spec (CommRingCat.of R))
    (h₀ : ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k₀)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k₀))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s₀)) (i₂ : SchemeHomOver c₂ (pullback.snd c s₀))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s₀), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s₀).1).base (IsLocalRing.closedPoint k₀) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀)) =
          connectedComponentIn ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀))
            (((sectionFibrePoint ε s₀).1).base (IsLocalRing.closedPoint k₀)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀)) =
          ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀)) \
            connectedComponentIn ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀))
              (((sectionFibrePoint ε s₀).1).base (IsLocalRing.closedPoint k₀)) ∧
        (∃ W₁ : (pullback c s₀).Opens, (W₁ : Set ↥(pullback c s₀)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s₀).Opens, (W₂ : Set ↥(pullback c s₀)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)))
    {k : Type u} [Field k] [IsAlgClosed k] (ι : k₀ →+* k)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (hs : s = Spec.map (CommRingCat.ofHom ι) ≫ s₀) :
    ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s)) (i₂ : SchemeHomOver c₂ (pullback.snd c s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
            connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
              (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s).Opens, (W₂ : Set ↥(pullback c s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)) := by
  subst hs
  obtain ⟨C₁, C₂, c₁, c₂, hp₁, hsm₁, hgi₁, hp₂, hsm₂, hgi₂, i₁, i₂, hci₁, hci₂, n, hjs, hred, hn, hn0, hεmem, hUeq,
    hUtr₁, hUtr₂, ⟨W₁, hW₁, hW₁oi⟩, ⟨W₂, hW₂, hW₂oi⟩⟩ := h₀

  set π : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k₀) := Spec.map (CommRingCat.ofHom ι) with hπ
  let e : pullback c (π ≫ s₀) ⟶ pullback c s₀ :=
    pullback.lift (pullback.fst c (π ≫ s₀)) (pullback.snd c (π ≫ s₀) ≫ π) (by rw [Category.assoc]; exact pullback.condition)
  have he_fst : e ≫ pullback.fst c s₀ = pullback.fst c (π ≫ s₀) := pullback.lift_fst _ _ _
  have he_snd : e ≫ pullback.snd c s₀ = pullback.snd c (π ≫ s₀) ≫ π := pullback.lift_snd _ _ _
  have hE : IsPullback e (pullback.snd c (π ≫ s₀)) (pullback.snd c s₀) π :=
    IsPullback.of_right (by rw [he_fst]; exact IsPullback.of_hasPullback c (π ≫ s₀)) he_snd
      (IsPullback.of_hasPullback c s₀)
  have hπsurj : Surjective π := ⟨Function.surjective_to_subsingleton _⟩
  have hesurj : Surjective e := MorphismProperty.of_isPullback hE.flip hπsurj

  let i₁' : pullback i₁.1 e ⟶ pullback c (π ≫ s₀) := pullback.snd i₁.1 e
  let i₂' : pullback i₂.1 e ⟶ pullback c (π ≫ s₀) := pullback.snd i₂.1 e
  let c₁' : pullback i₁.1 e ⟶ Spec (CommRingCat.of k) := i₁' ≫ pullback.snd c (π ≫ s₀)
  let c₂' : pullback i₂.1 e ⟶ Spec (CommRingCat.of k) := i₂' ≫ pullback.snd c (π ≫ s₀)
  have sq₁ : IsPullback (pullback.fst i₁.1 e) c₁' c₁ π := by
    have := (IsPullback.of_hasPullback i₁.1 e).paste_vert hE
    rwa [i₁.2] at this
  have sq₂ : IsPullback (pullback.fst i₂.1 e) c₂' c₂ π := by
    have := (IsPullback.of_hasPullback i₂.1 e).paste_vert hE
    rwa [i₂.2] at this
  have hp₁' : IsProper c₁' := MorphismProperty.of_isPullback sq₁ hp₁
  have hp₂' : IsProper c₂' := MorphismProperty.of_isPullback sq₂ hp₂
  have hsm₁' : SmoothOfRelativeDimension 1 c₁' :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback sq₁ hsm₁
  have hsm₂' : SmoothOfRelativeDimension 1 c₂' :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback sq₂ hsm₂
  have hgi₁' : GeometricallyIntegral c₁' := MorphismProperty.of_isPullback sq₁ hgi₁
  have hgi₂' : GeometricallyIntegral c₂' := MorphismProperty.of_isPullback sq₂ hgi₂
  have hci₁' : IsClosedImmersion i₁' := inferInstance
  have hci₂' : IsClosedImmersion i₂' := inferInstance

  have hr₁ : Set.range i₁'.base = e.base ⁻¹' Set.range i₁.1.base := Scheme.Pullback.range_snd i₁.1 e
  have hr₂ : Set.range i₂'.base = e.base ⁻¹' Set.range i₂.1.base := Scheme.Pullback.range_snd i₂.1 e

  set V₀ : Set ↥(pullback c s₀) := ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀))
    with hV₀def
  set V : Set ↥(pullback c (π ≫ s₀)) :=
    ((pullback.fst c (π ≫ s₀) ⁻¹ᵁ U : (pullback c (π ≫ s₀)).Opens) : Set ↥(pullback c (π ≫ s₀))) with hVdef
  have hV : V = e.base ⁻¹' V₀ := by
    rw [hVdef, hV₀def, ← he_fst, Scheme.Hom.comp_preimage]; rfl
  have hVopen : IsOpen V := (pullback.fst c (π ≫ s₀) ⁻¹ᵁ U).isOpen

  set pt₀ := ((sectionFibrePoint ε s₀).1).base (IsLocalRing.closedPoint k₀) with hpt₀def
  set pt := ((sectionFibrePoint ε (π ≫ s₀)).1).base (IsLocalRing.closedPoint k) with hptdef
  have hsec : (sectionFibrePoint ε (π ≫ s₀)).1 ≫ e = π ≫ (sectionFibrePoint ε s₀).1 := by
    apply pullback.hom_ext
    · simp only [Category.assoc, he_fst, sectionFibrePoint, pullback.lift_fst]
    · simp only [Category.assoc, he_snd, sectionFibrePoint, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.id_comp, Category.comp_id]
  have hpt : e.base pt = pt₀ := by
    rw [hptdef, hpt₀def]
    change ((sectionFibrePoint ε (π ≫ s₀)).1 ≫ e).base (IsLocalRing.closedPoint k) = _
    rw [hsec]
    change ((sectionFibrePoint ε s₀).1).base (π.base (IsLocalRing.closedPoint k)) = _
    rw [Subsingleton.elim (π.base (IsLocalRing.closedPoint k)) (IsLocalRing.closedPoint k₀)]

  let p : pullback i₁' i₂' ⟶ pullback i₁.1 i₂.1 :=
    pullback.map i₁' i₂' i₁.1 i₂.1 (pullback.fst i₁.1 e) (pullback.fst i₂.1 e) e
      pullback.condition.symm pullback.condition.symm
  have hp_fst : p ≫ pullback.fst i₁.1 i₂.1 = pullback.fst i₁' i₂' ≫ pullback.fst i₁.1 e := pullback.lift_fst _ _ _
  have hp_snd : p ≫ pullback.snd i₁.1 i₂.1 = pullback.snd i₁' i₂' ≫ pullback.fst i₂.1 e := pullback.lift_snd _ _ _

  have S3 : IsPullback (pullback.snd i₁' i₂' ≫ pullback.fst i₂.1 e) (pullback.fst i₁' i₂') i₂.1
      (pullback.fst i₁.1 e ≫ i₁.1) := by
    have := (IsPullback.of_hasPullback i₁' i₂').flip.paste_horiz (IsPullback.of_hasPullback i₂.1 e)
    rwa [show i₁' ≫ e = pullback.fst i₁.1 e ≫ i₁.1 from pullback.condition.symm] at this

  have S4 : IsPullback (pullback.fst i₁' i₂') p (pullback.fst i₁.1 e) (pullback.fst i₁.1 i₂.1) :=
    IsPullback.of_bot (by rw [hp_snd]; exact S3.flip) hp_fst.symm (IsPullback.of_hasPullback i₁.1 i₂.1)

  let z : pullback i₁.1 i₂.1 ⟶ Spec (CommRingCat.of k₀) := pullback.fst i₁.1 i₂.1 ≫ c₁
  have SP : IsPullback p (pullback.fst i₁' i₂' ≫ c₁') z π := S4.flip.paste_vert sq₁
  let m : pullback i₁' i₂' ≅ pullback z π := SP.isoPullback

  haveI : IsReduced (pullback i₁.1 i₂.1) := hred
  haveI : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by rw [hn]; exact hn0.ne')
  haveI : Smooth c₁ := SmoothOfRelativeDimension.smooth 1 c₁
  haveI : LocallyOfFiniteType z := inferInstance
  obtain ⟨hred', hcard'⟩ := AlgebraicGeometry.isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed z ι

  have hcl₁ : IsClosed (Set.range i₁'.base) := i₁'.isClosedEmbedding.isClosed_range
  have hcl₂ : IsClosed (Set.range i₂'.base) := i₂'.isClosedEmbedding.isClosed_range
  have hpt₀V : pt₀ ∈ V₀ := by
    rw [hUeq, Scheme.Pullback.range_fst_comp]
    exact fun h => hεmem.2 h.2
  have hptV : pt ∈ V := by rw [hV, Set.mem_preimage, hpt]; exact hpt₀V
  have hA : Set.range i₁'.base ∩ V = e.base ⁻¹' connectedComponentIn V₀ pt₀ := by
    rw [hr₁, hV, ← Set.preimage_inter, hUtr₁]
  have hB : Set.range i₂'.base ∩ V = V \ e.base ⁻¹' connectedComponentIn V₀ pt₀ := by
    rw [hr₂, hV, ← Set.preimage_inter, hUtr₂, Set.preimage_diff]
  have hptA : pt ∈ Set.range i₁'.base ∩ V := by
    rw [hA, Set.mem_preimage, hpt]; exact mem_connectedComponentIn hpt₀V

  haveI : IrreducibleSpace ↥(pullback i₁.1 e) := GeometricallyIrreducible.irreducibleSpace_of_subsingleton c₁'
  have hApre : IsPreconnected (Set.range i₁'.base ∩ V) := by
    rw [← Set.image_preimage_eq_range_inter]
    refine IsPreconnected.image ?_ _ i₁'.base.hom.continuous.continuousOn
    exact ((IrreducibleSpace.isIrreducible_univ _).isPreirreducible.open_subset
      (hVopen.preimage i₁'.base.hom.continuous) (Set.subset_univ _)).isPreconnected
  have hcc : Set.range i₁'.base ∩ V = connectedComponentIn V pt := by
    apply Set.Subset.antisymm
    · exact hApre.subset_connectedComponentIn hptA Set.inter_subset_right
    ·
      have hu : IsOpen (V ∩ (Set.range i₂'.base)ᶜ) := hVopen.inter hcl₂.isOpen_compl
      have hv : IsOpen (V ∩ (Set.range i₁'.base)ᶜ) := hVopen.inter hcl₁.isOpen_compl
      have hAeq : Set.range i₁'.base ∩ V = V ∩ (Set.range i₂'.base)ᶜ := by
        ext x
        constructor
        · rintro ⟨hx1, hxV⟩
          refine ⟨hxV, fun hx2 => ?_⟩
          have h2 : x ∈ Set.range i₂'.base ∩ V := ⟨hx2, hxV⟩
          have h1 : x ∈ Set.range i₁'.base ∩ V := ⟨hx1, hxV⟩
          rw [hB] at h2
          rw [hA] at h1
          exact h2.2 h1
        · rintro ⟨hxV, hx2⟩
          by_contra hx1
          have : x ∈ Set.range i₂'.base ∩ V := by
            rw [hB]; refine ⟨hxV, fun h => hx1 ?_⟩
            rw [hA]; exact h
          exact hx2 this.1
      have huv : Disjoint (V ∩ (Set.range i₂'.base)ᶜ) (V ∩ (Set.range i₁'.base)ᶜ) := by
        rw [Set.disjoint_left]
        rintro x ⟨hxV, hx2⟩ ⟨-, hx1⟩
        rcases hjs (e.base x) with h | h
        · exact hx1 (by rw [hr₁]; exact h)
        · exact hx2 (by rw [hr₂]; exact h)
      have hsub : connectedComponentIn V pt ⊆ V ∩ (Set.range i₂'.base)ᶜ ∪ V ∩ (Set.range i₁'.base)ᶜ := by
        intro x hx
        have hxV : x ∈ V := connectedComponentIn_subset _ _ hx
        by_cases h1 : x ∈ Set.range i₁'.base
        · left; rw [← hAeq]; exact ⟨h1, hxV⟩
        · right; exact ⟨hxV, h1⟩
      have hne : (connectedComponentIn V pt ∩ (V ∩ (Set.range i₂'.base)ᶜ)).Nonempty :=
        ⟨pt, mem_connectedComponentIn hptV, hAeq ▸ hptA⟩
      rw [hAeq]
      exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hu hv huv hsub hne

  have hOI : ∀ {D : Scheme.{u}} (i : D ⟶ pullback c s₀) (W : (pullback c s₀).Opens),
      IsOpenImmersion ((i ⁻¹ᵁ W).ι ≫ i) →
      IsOpenImmersion (((pullback.snd i e) ⁻¹ᵁ (e ⁻¹ᵁ W)).ι ≫ pullback.snd i e) := by
    intro D i W hW
    have heqO : (pullback.snd i e) ⁻¹ᵁ (e ⁻¹ᵁ W) = (pullback.fst i e) ⁻¹ᵁ (i ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
    have sq : IsPullback (pullback.snd (pullback.fst i e) (i ⁻¹ᵁ W).ι)
        (pullback.fst (pullback.fst i e) (i ⁻¹ᵁ W).ι ≫ pullback.snd i e) ((i ⁻¹ᵁ W).ι ≫ i) e :=
      ((IsPullback.of_hasPullback (pullback.fst i e) (i ⁻¹ᵁ W).ι).paste_horiz
        (IsPullback.of_hasPullback i e).flip).flip
    have h1 : IsOpenImmersion (pullback.fst (pullback.fst i e) (i ⁻¹ᵁ W).ι ≫ pullback.snd i e) :=
      MorphismProperty.of_isPullback sq hW
    have h2 : IsOpenImmersion (((pullback.fst i e) ⁻¹ᵁ (i ⁻¹ᵁ W)).ι ≫ pullback.snd i e) := by
      rw [← pullbackRestrictIsoRestrict_inv_fst, Category.assoc]; infer_instance
    have h3 : ((pullback.snd i e) ⁻¹ᵁ (e ⁻¹ᵁ W)).ι ≫ pullback.snd i e =
        (Scheme.isoOfEq _ heqO).hom ≫ ((pullback.fst i e) ⁻¹ᵁ (i ⁻¹ᵁ W)).ι ≫ pullback.snd i e := by
      rw [Scheme.isoOfEq_hom_ι_assoc]
    rw [h3]; infer_instance

  refine ⟨pullback i₁.1 e, pullback i₂.1 e, c₁', c₂', hp₁', hsm₁', hgi₁', hp₂', hsm₂', hgi₂', ⟨i₁', rfl⟩, ⟨i₂', rfl⟩,
    hci₁', hci₂', n, ?_, ?_, ?_, hn0, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro x
    rcases hjs (e.base x) with h | h
    · left; show x ∈ Set.range i₁'.base; rw [hr₁]; exact h
    · right; show x ∈ Set.range i₂'.base; rw [hr₂]; exact h

  · show IsReduced (pullback i₁' i₂')
    exact isReduced_of_isOpenImmersion m.hom

  · show Nat.card ↥(pullback i₁' i₂') = n
    rw [← hn, ← hcard']
    exact Nat.card_congr (Scheme.homeoOfIso m).toEquiv

  · show pt ∈ Set.range i₁'.base \ Set.range i₂'.base
    rw [hr₁, hr₂, ← Set.preimage_diff, Set.mem_preimage, hpt]
    exact hεmem

  · show V = (Set.range (pullback.fst i₁' i₂' ≫ i₁').base)ᶜ
    rw [Scheme.Pullback.range_fst_comp, hV, hUeq, Scheme.Pullback.range_fst_comp, hr₁, hr₂,
      Set.preimage_compl, Set.preimage_inter]

  · exact hcc

  · show Set.range i₂'.base ∩ V = V \ connectedComponentIn V pt
    rw [← hcc, hB, hA]

  · refine ⟨e ⁻¹ᵁ W₁, ?_, hOI i₁.1 W₁ hW₁oi⟩
    show e.base ⁻¹' (W₁ : Set ↥(pullback c s₀)) = (Set.range i₂'.base)ᶜ
    rw [hW₁, Set.preimage_compl, ← hr₂]

  · refine ⟨e ⁻¹ᵁ W₂, ?_, hOI i₂.1 W₂ hW₂oi⟩
    show e.base ⁻¹' (W₂ : Set ↥(pullback c s₀)) = (Set.range i₁'.base)ᶜ
    rw [hW₂, Set.preimage_compl, ← hr₁]

end S_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed (solution)
