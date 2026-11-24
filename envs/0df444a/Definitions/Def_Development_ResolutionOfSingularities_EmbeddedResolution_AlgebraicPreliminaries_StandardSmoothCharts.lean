-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_StandardSmoothCharts
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_StandardSmoothCharts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:31.638799+00:00
-- url     : https://prove2.me/theorems/98e20fa0-a621-433b-86cf-671682770387
-- title:
--   Standard Smooth Charts
-- statement:
--   Definitions and structural lemmas for Standard Smooth Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/StandardSmoothCharts.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
theorem preimage_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  simp
theorem image_preimage_of_le {X : Scheme.{u}} (U A : X.Opens) (hA : A ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ A) = A := by
  apply le_antisymm
  · rintro z ⟨w, hw, rfl⟩
    exact hw
  · intro z hz
    exact ⟨⟨z, hA hz⟩, hz, rfl⟩
theorem basicOpen_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (s : ↑(Y.presheaf.obj (Opposite.op U))) :
    X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s) =
      V ⊓ f ⁻¹ᵁ Y.basicOpen s := by
  simp [AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.preimage_basicOpen]
theorem algebraMap_basicOpen_eq_presheaf_map {X : Scheme.{u}} {U : X.Opens}
    (s : ↑(X.presheaf.obj (Opposite.op U))) :
    algebraMap ↑(X.presheaf.obj (Opposite.op U))
        ↑(X.presheaf.obj (Opposite.op (X.basicOpen s))) =
      (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom :=
  rfl
theorem isStandardSmoothOfRelativeDimension_appLE_basicOpen_target {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) {U : Y.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {V : X.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (s : ↑(Y.presheaf.obj (Opposite.op U)))
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom)
    (hle : X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s) ≤
      f ⁻¹ᵁ Y.basicOpen s) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f (Y.basicOpen s)
        (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)) hle).hom := by
  have i1 : IsLocalization.Away s ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen s))) :=
    hU.isLocalization_basicOpen s
  have i2 : IsLocalization.Away ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)
      ↑(X.presheaf.obj (Opposite.op
        (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)))) :=
    hV.isLocalization_basicOpen _
  have i3 : IsLocalization
      (Submonoid.map (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom (Submonoid.powers s))
      ↑(X.presheaf.obj (Opposite.op
        (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)))) := by
    rw [Submonoid.map_powers]
    exact i2
  have key := RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves n
    (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom (Submonoid.powers s)
    ↑(Y.presheaf.obj (Opposite.op (Y.basicOpen s)))
    ↑(X.presheaf.obj (Opposite.op
      (X.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom s)))) hs
  convert key using 1
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  rw [IsLocalization.map_comp, algebraMap_basicOpen_eq_presheaf_map,
    algebraMap_basicOpen_eq_presheaf_map, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, AlgebraicGeometry.Scheme.Hom.map_appLE,
    AlgebraicGeometry.Scheme.Hom.appLE_map]
theorem isStandardSmoothOfRelativeDimension_appLE_basicOpen_source {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) {U : Y.Opens}
    {V : X.Opens} (hV : AlgebraicGeometry.IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom)
    (t : ↑(X.presheaf.obj (Opposite.op V))) (hle : X.basicOpen t ≤ f ⁻¹ᵁ U) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U (X.basicOpen t) hle).hom := by
  have : IsLocalization.Away t ↑(X.presheaf.obj (Opposite.op (X.basicOpen t))) :=
    hV.isLocalization_basicOpen t
  have h0 : RingHom.IsStandardSmoothOfRelativeDimension 0
      (algebraMap ↑(X.presheaf.obj (Opposite.op V))
        ↑(X.presheaf.obj (Opposite.op (X.basicOpen t)))) :=
    RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway _ t
  have hcomp := h0.comp hs
  rw [zero_add, algebraMap_basicOpen_eq_presheaf_map, ← CommRingCat.hom_comp,
    AlgebraicGeometry.Scheme.Hom.appLE_map] at hcomp
  exact hcomp
theorem isStandardSmoothOfRelativeDimension_appLE_congr {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) {U U' : Y.Opens}
    {V V' : X.Opens} (hU : U' = U) (hV : V' = V) (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U')
    (hstd : RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U V e).hom) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      (AlgebraicGeometry.Scheme.Hom.appLE f U' V' e').hom := by
  subst hU
  subst hV
  exact hstd
theorem exists_affineChart_isStandardSmoothOfRelativeDimension {X X' : Scheme.{u}}
    (φ : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension r φ] (A₀ : X.Opens) (B₀ : X'.Opens)
    (hB₀ : B₀ ≤ φ ⁻¹ᵁ A₀) (y : ↥X') (hy : y ∈ B₀) :
    ∃ (A : X.Opens) (B : X'.Opens), AlgebraicGeometry.IsAffineOpen A ∧
      AlgebraicGeometry.IsAffineOpen B ∧ A ≤ A₀ ∧ B ≤ B₀ ∧ y ∈ B ∧
      ∃ e : B ≤ φ ⁻¹ᵁ A, RingHom.IsStandardSmoothOfRelativeDimension r
        (AlgebraicGeometry.Scheme.Hom.appLE φ A B e).hom := by
  obtain ⟨U, hU, V, hV, hyV, e, hstd⟩ :=
    (AlgebraicGeometry.smoothOfRelativeDimension_iff r φ).mp inferInstance y
  obtain ⟨s, hsA₀, hys⟩ := hU.exists_basicOpen_le (⟨φ.base y, hB₀ hy⟩ : ↥A₀) (e hyV)
  have hB₁eq : X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) =
      V ⊓ φ ⁻¹ᵁ X.basicOpen s := basicOpen_appLE φ e s
  have hB₁le : X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) ≤
      φ ⁻¹ᵁ X.basicOpen s := by
    rw [hB₁eq]
    exact inf_le_right
  have hB₁aff : AlgebraicGeometry.IsAffineOpen
      (X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s)) := hV.basicOpen _
  have hyB₁ : y ∈ X'.basicOpen ((AlgebraicGeometry.Scheme.Hom.appLE φ U V e).hom s) := by
    rw [hB₁eq]
    exact ⟨hyV, hys⟩
  have hstd₁ :=
    isStandardSmoothOfRelativeDimension_appLE_basicOpen_target φ r hU hV e s hstd hB₁le
  obtain ⟨t, htB₀, hyt⟩ := hB₁aff.exists_basicOpen_le (⟨y, hy⟩ : ↥B₀) hyB₁
  have hBle : X'.basicOpen t ≤ φ ⁻¹ᵁ X.basicOpen s :=
    le_trans (X'.basicOpen_le t) hB₁le
  exact ⟨X.basicOpen s, X'.basicOpen t, hU.basicOpen s, hB₁aff.basicOpen t, hsA₀, htB₀, hyt,
    hBle, isStandardSmoothOfRelativeDimension_appLE_basicOpen_source φ r hB₁aff hB₁le hstd₁ t hBle⟩
theorem smoothOfRelativeDimension_resLE {X X' : Scheme.{u}} (φ : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension r φ] (U₀ : X.Opens) (V₀ : X'.Opens)
    (h : V₀ ≤ φ ⁻¹ᵁ U₀) :
    AlgebraicGeometry.SmoothOfRelativeDimension r (φ.resLE U₀ V₀ h) := by
  rw [AlgebraicGeometry.smoothOfRelativeDimension_iff]
  intro x
  have hx : V₀.ι.base x ∈ V₀ := by
    have hmem : V₀.ι.base x ∈ AlgebraicGeometry.Scheme.Hom.opensRange V₀.ι := ⟨x, rfl⟩
    rwa [AlgebraicGeometry.Scheme.Opens.opensRange_ι] at hmem
  obtain ⟨A, B, hA, hB, hAU₀, hBV₀, hxB, e, hstd⟩ :=
    exists_affineChart_isStandardSmoothOfRelativeDimension φ r U₀ V₀ h (V₀.ι.base x) hx
  have hpre : (φ.resLE U₀ V₀ h) ⁻¹ᵁ (U₀.ι ⁻¹ᵁ A) = V₀.ι ⁻¹ᵁ (φ ⁻¹ᵁ A) := by
    rw [← preimage_comp, ← preimage_comp, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]
  have he' : V₀.ι ⁻¹ᵁ B ≤ (φ.resLE U₀ V₀ h) ⁻¹ᵁ (U₀.ι ⁻¹ᵁ A) := by
    rw [hpre]
    exact fun z hz => e hz
  refine ⟨U₀.ι ⁻¹ᵁ A, hA.preimage_of_isOpenImmersion U₀.ι (by simp [hAU₀]),
    V₀.ι ⁻¹ᵁ B, hB.preimage_of_isOpenImmersion V₀.ι (by simp [hBV₀]), hxB, he', ?_⟩
  rw [AlgebraicGeometry.Scheme.Hom.resLE_appLE]
  exact isStandardSmoothOfRelativeDimension_appLE_congr φ r (image_preimage_of_le U₀ A hAU₀)
    (image_preimage_of_le V₀ B hBV₀) e _ hstd
instance instSmoothOfRelativeDimensionResLE {X X' : Scheme.{u}} (φ : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension r φ] (U₀ : X.Opens) (V₀ : X'.Opens)
    (h : V₀ ≤ φ ⁻¹ᵁ U₀) :
    AlgebraicGeometry.SmoothOfRelativeDimension r (φ.resLE U₀ V₀ h) :=
  smoothOfRelativeDimension_resLE φ r U₀ V₀ h
end FunctorialResolution.EmbeddedResolution


