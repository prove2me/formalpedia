-- Prove2me | solution 1 for AlgebraicGeometry.AffineLimit.locallyOfFiniteType_of_forall_exists_fg_factor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/9078027d-f543-5bcb-bdcc-dc469d317e1d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution {R : Type u} [CommRing R] {X : Scheme.{u}}
    (ξ : X ⟶ Spec (CommRingCat.of R))
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A] (φ : Spec (CommRingCat.of A) ⟶ X),
      φ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
      ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (φ₀ : Spec (CommRingCat.of ↥A₀) ⟶ X),
        φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀)) ∧
        Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = φ) :
    LocallyOfFiniteType ξ := by
  classical

  suffices key : ∀ p : X, ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (_ : IsOpenImmersion j),
      p ∈ Set.range ⇑j ∧ LocallyOfFiniteType (j ≫ ξ) by
    choose Y j hj hmem hlft using key
    exact IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
      (Scheme.Cover.mkOfCovers X Y j (fun x => ⟨x, hmem x⟩) (fun x => hj x)) hlft
  intro p

  obtain ⟨B, ι, hι, y, hy⟩ : ∃ (B : CommRingCat.{u}) (ι : Spec B ⟶ X) (_ : IsOpenImmersion ι) (y : Spec B), ι y = p := by
    obtain ⟨V, hV, hpV, -⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ p ∈ V ∧ V ≤ ⊤ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) (show p ∈ (⊤ : X.Opens) from trivial)
    refine ⟨Γ(X, V), hV.isoSpec.inv ≫ V.ι, inferInstance, hV.isoSpec.hom ⟨p, hpV⟩, ?_⟩
    rw [Scheme.Hom.comp_apply]
    simp
  letI : Algebra R B := (Spec.preimage (ι ≫ ξ)).hom.toAlgebra
  have hιξ : ι ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]

  obtain ⟨B₀, hB₀, φ₀, hφ₀, hfac⟩ := h B ι hιξ
  haveI : Algebra.FiniteType R ↥B₀ := (Subalgebra.fg_iff_finiteType B₀).mp hB₀

  have hq : (Spec.map (CommRingCat.ofHom B₀.val.toRingHom)) y ∈ φ₀ ⁻¹ᵁ ι.opensRange := by
    show φ₀ (Spec.map (CommRingCat.ofHom B₀.val.toRingHom) y) ∈ ι.opensRange
    rw [← Scheme.Hom.comp_apply, hfac]
    exact ⟨y, rfl⟩
  obtain ⟨_, ⟨f₀, rfl⟩, hqf, hfU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) hq

  let f : B := (f₀ : B)
  let j₀ : Spec (CommRingCat.of (Localization.Away f₀)) ⟶ Spec (CommRingCat.of ↥B₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥B₀ (Localization.Away f₀)))
  let jB : Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec B :=
    Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away f)))
  have hpow : Submonoid.powers f₀ ≤ (Submonoid.powers f).comap B₀.val.toRingHom := by
    rintro _ ⟨n, rfl⟩; exact ⟨n, by simp [f]⟩
  let g : Localization.Away f₀ →+* Localization.Away f :=
    IsLocalization.map (Localization.Away f) B₀.val.toRingHom hpow
  have hsq : jB ≫ Spec.map (CommRingCat.ofHom B₀.val.toRingHom) = Spec.map (CommRingCat.ofHom g) ≫ j₀ := by
    simp only [jB, j₀, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (IsLocalization.map_comp hpow).symm

  have hrange : Set.range ⇑(j₀ ≫ φ₀) ⊆ Set.range ⇑ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    have hz : j₀ z ∈ (PrimeSpectrum.basicOpen f₀ : Set (PrimeSpectrum ↥B₀)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f₀) f₀]
      exact ⟨z, rfl⟩
    have := hfU hz
    rwa [← Scheme.Hom.coe_opensRange]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : B →+* Localization.Away f₀, Spec.map (CommRingCat.ofHom ρ) ≫ ι = j₀ ≫ φ₀ :=
    ⟨(Spec.preimage (IsOpenImmersion.lift ι (j₀ ≫ φ₀) hrange)).hom, by
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩

  have hcomp : g.comp ρ = algebraMap B (Localization.Away f) := by
    have h1 : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom ρ) = jB := by
      rw [← cancel_mono ι, Category.assoc, hρ, ← Category.assoc, ← hsq, Category.assoc, hfac]
    have h2 := Spec.map_injective ((Spec.map_comp _ _).trans h1)
    exact congrArg CommRingCat.Hom.hom h2

  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) z
    refine ⟨ρ b * IsLocalization.mk' (Localization.Away f₀) 1 (⟨f₀ ^ n, n, rfl⟩ : Submonoid.powers f₀), ?_⟩
    have e1 : g (ρ b) = algebraMap B (Localization.Away f) b := by rw [← RingHom.comp_apply, hcomp]
    have e2 : g (IsLocalization.mk' (Localization.Away f₀) 1 (⟨f₀ ^ n, n, rfl⟩ : Submonoid.powers f₀)) =
        IsLocalization.mk' (Localization.Away f) 1 (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) := by
      rw [IsLocalization.map_mk']
      rfl
    show g (_ * _) = IsLocalization.mk' (Localization.Away f) b (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
    rw [map_mul, e1, e2, ← IsLocalization.mk'_eq_mul_mk'_one]
  letI : Algebra R (Localization.Away f₀) := inferInstance
  have hgR : ∀ r : R, g (algebraMap R (Localization.Away f₀) r) = algebraMap R (Localization.Away f) r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R ↥B₀ (Localization.Away f₀), IsScalarTower.algebraMap_apply R B (Localization.Away f)]
    change (g.comp (algebraMap ↥B₀ (Localization.Away f₀))) _ = _
    rw [IsLocalization.map_comp hpow]
    rfl
  let gₐ : Localization.Away f₀ →ₐ[R] Localization.Away f := { g with commutes' := hgR }
  haveI : Algebra.FiniteType R (Localization.Away f) := Algebra.FiniteType.of_surjective gₐ hsurj

  refine ⟨Spec (CommRingCat.of (Localization.Away f)), jB ≫ ι, inferInstance, ?_, ?_⟩
  ·
    have hyf : y ∈ Set.range ⇑jB := by
      change y ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away f)))
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact hqf
    obtain ⟨z, hz⟩ := hyf
    exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hy]⟩
  · rw [Category.assoc, hιξ, show jB ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R (↑B) (Localization.Away f)]]
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom]
    exact RingHom.finiteType_algebraMap.mpr inferInstance

end S_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor
end P2MW
export P2MW.S_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor (solution)
