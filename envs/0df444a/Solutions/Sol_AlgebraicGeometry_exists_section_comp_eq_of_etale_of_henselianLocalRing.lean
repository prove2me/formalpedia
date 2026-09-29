-- Prove2me | solution 1 for AlgebraicGeometry.exists_section_comp_eq_of_etale_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5f76750a-f7b4-5782-ab02-12b4eee6e939

import Mathlib
import Theorems.Thm_HenselianLocalRing_exists_algHom_lift_of_etale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_section_comp_eq_of_etale_of_henselianLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace F2Proof

theorem affine_case {R : Type u} [CommRing R] [HenselianLocalRing R] {B : CommRingCat.{u}}
    (g : Spec B ⟶ Spec (CommRingCat.of R)) [Etale g]
    (e : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec B)
    (he : e ≫ g = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ Spec B, s ≫ g = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ s = e := by
  let ψ₀ : CommRingCat.of R ⟶ B := Spec.preimage g
  have hψ₀ : Spec.map ψ₀ = g := Spec.map_preimage g
  let χ : B ⟶ CommRingCat.of (IsLocalRing.ResidueField R) := Spec.preimage e
  have hχ : Spec.map χ = e := Spec.map_preimage e
  have hcomp : ψ₀ ≫ χ = CommRingCat.ofHom (IsLocalRing.residue R) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hχ, hψ₀, he]
  letI alg : Algebra R B := ψ₀.hom.toAlgebra
  haveI : Algebra.Etale R B := by
    have hE : Etale (Spec.map ψ₀) := by rw [hψ₀]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hE
  have hcomp' : ∀ r : R, χ.hom (ψ₀.hom r) = IsLocalRing.residue R r := by
    intro r
    have := congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of (IsLocalRing.ResidueField R) => k.hom r) hcomp
    simpa using this
  let φ : B →ₐ[R] IsLocalRing.ResidueField R :=
    { χ.hom with commutes' := fun r => hcomp' r }
  obtain ⟨σ, hσ⟩ := HenselianLocalRing.exists_algHom_lift_of_etale (R := R) B φ
  refine ⟨Spec.map (CommRingCat.ofHom σ.toRingHom), ?_, ?_⟩
  · rw [← hψ₀, ← Spec.map_comp]
    have hid : ψ₀ ≫ CommRingCat.ofHom σ.toRingHom = 𝟙 _ := by
      ext r
      change σ (ψ₀.hom r) = r
      exact σ.commutes r
    rw [hid, Spec.map_id]
  · rw [← Spec.map_comp, ← hχ]
    congr 1
    ext b
    change IsLocalRing.residue R (σ b) = χ.hom b
    exact hσ b

theorem general {R : Type u} [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Etale f]
    (e : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ X)
    (he : e ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ s = e := by
  let κ := IsLocalRing.ResidueField R
  let x₀ : X := e.base (IsLocalRing.closedPoint κ)
  let j := X.affineCover.idx x₀
  let ι : X.affineCover.X j ⟶ X := X.affineCover.f j
  have hx₀ : x₀ ∈ Set.range ι.base := X.affineCover.covers x₀
  have hrange : Set.range e.base ⊆ Set.range ι.base := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint κ := Subsingleton.elim _ _
    rw [hp]
    exact hx₀
  let e1 := IsOpenImmersion.lift ι e hrange
  have he1 : e1 ≫ ι = e := IsOpenImmersion.lift_fac ι e hrange
  have he1g : e1 ≫ (ι ≫ f) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
    rw [← Category.assoc, he1, he]
  haveI hι : IsOpenImmersion ι := X.affineCover.map_prop j
  have hEt : Etale (ι ≫ f) := inferInstance
  obtain ⟨s, hs1, hs2⟩ := @affine_case R _ _ _ (ι ≫ f) hEt e1 he1g
  refine ⟨s ≫ ι, ?_, ?_⟩
  · rw [Category.assoc, hs1]
  · rw [← Category.assoc, hs2]
    exact he1

end F2Proof

theorem solution {R : Type u} [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [AlgebraicGeometry.Etale f]
    (e : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ X)
    (he : e ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ s = e :=
  F2Proof.general f e he

end S_AlgebraicGeometry_exists_section_comp_eq_of_etale_of_henselianLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_exists_section_comp_eq_of_etale_of_henselianLocalRing (solution)
