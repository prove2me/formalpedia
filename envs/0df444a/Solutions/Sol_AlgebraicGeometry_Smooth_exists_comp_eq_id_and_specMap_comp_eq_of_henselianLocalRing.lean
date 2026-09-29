-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/fbbd0b25-6bad-5057-b466-d4536e8cf7e3

import Mathlib
import Theorems.Thm_HenselianLocalRing_exists_algHom_lift_of_isSmoothAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing

set_option autoImplicit false

universe u

open IsLocalRing CategoryTheory AlgebraicGeometry

namespace HenselSmoothSection

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

theorem exists_lift_of_smooth
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (φ : S →ₐ[R] ResidueField R) :
    ∃ ψ : S →ₐ[R] R, ∀ s, algebraMap R (ResidueField R) (ψ s) = φ s := by
  haveI := RingHom.ker_isPrime φ
  exact HenselianLocalRing.exists_algHom_lift_of_isSmoothAt S φ

theorem exists_section {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x₀ : Spec (CommRingCat.of (ResidueField R)) ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))) ≫ s = x₀ := by

  let x : X := x₀.base (IsLocalRing.closedPoint (ResidueField R))
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let ι : Spec Γ(X, V) ⟶ X := hV.fromSpec

  have hrange : Set.range x₀.base ⊆ Set.range ι.base := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint (ResidueField R) := Subsingleton.elim _ _
    rw [hV.range_fromSpec]
    exact hxV
  let y₀ : Spec (CommRingCat.of (ResidueField R)) ⟶ Spec Γ(X, V) :=
    IsOpenImmersion.lift ι x₀ hrange
  have hy₀ : y₀ ≫ ι = x₀ := IsOpenImmersion.lift_fac ι x₀ hrange

  let g : Spec Γ(X, V) ⟶ Spec (CommRingCat.of R) := ι ≫ f
  let φ : CommRingCat.of R ⟶ Γ(X, V) := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  let π : Γ(X, V) ⟶ CommRingCat.of (ResidueField R) := Spec.preimage y₀
  have hπ : Spec.map π = y₀ := Spec.map_preimage y₀
  have hcomp : φ ≫ π = CommRingCat.ofHom (algebraMap R (ResidueField R)) := by
    rw [← Spec.map_inj, Spec.map_comp, hπ, hφ]
    change y₀ ≫ ι ≫ f = _
    rw [← Category.assoc, hy₀, hx₀]

  have hs : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at hs

  letI : Algebra R Γ(X, V) := φ.hom.toAlgebra
  haveI : Algebra.Smooth R Γ(X, V) := hs
  let πa : Γ(X, V) →ₐ[R] ResidueField R :=
    { π.hom with
      commutes' := fun r => by
        change π.hom (φ.hom r) = algebraMap R (ResidueField R) r
        rw [← CommRingCat.comp_apply, hcomp]
        rfl }
  obtain ⟨ψ, hψ⟩ := exists_lift_of_smooth (R := R) Γ(X, V) πa
  have hψφ : φ ≫ CommRingCat.ofHom ψ.toRingHom = 𝟙 _ := by
    ext r
    change ψ (φ.hom r) = r
    exact ψ.commutes r
  have hψπ : CommRingCat.ofHom ψ.toRingHom ≫
      CommRingCat.ofHom (algebraMap R (ResidueField R)) = π := by
    ext a
    exact hψ a
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ι, ?_, ?_⟩
  · change Spec.map _ ≫ g = 𝟙 _
    rw [← hφ, ← Spec.map_comp, hψφ, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hψπ, hπ, hy₀]

end HenselSmoothSection

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x₀ : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ X)
    (hx₀ : x₀ ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ s = x₀ :=
  HenselSmoothSection.exists_section f x₀ hx₀

end S_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing (solution)
