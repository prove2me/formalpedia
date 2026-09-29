-- Prove2me | solution 1 for AlgebraicGeometry.frobenius_comp_eq_comp_frobenius_of_forall_spec
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/53f93561-6249-5ae8-8a36-e4fad44dfd59

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_frobenius_comp_eq_comp_frobenius_of_forall_spec

set_option autoImplicit false

namespace Ws23
namespace FrobNat

open AlgebraicGeometry CategoryTheory

universe u

theorem piece (p : ℕ) [Fact p.Prime] {X Y : Scheme.{0}}
    (fX : X ⟶ Spec (CommRingCat.of (ZMod p))) (fY : Y ⟶ Spec (CommRingCat.of (ZMod p)))
    (FX : X ⟶ X) (FY : Y ⟶ Y)
    (hFX : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ FX)
    (hFY : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (y : Spec (CommRingCat.of B) ⟶ Y),
        y ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ y = y ≫ FY)
    (g : X ⟶ Y) (hg : g ≫ fY = fX) {R : CommRingCat.{0}} (ι : Spec R ⟶ X) :
    ι ≫ (FX ≫ g) = ι ≫ (g ≫ FY) := by

  letI : Algebra (ZMod p) R := (Spec.preimage (ι ≫ fX)).hom.toAlgebra
  have hx : ι ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) R)) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  by_cases hR : Nontrivial R
  · haveI : CharP R p := charP_of_injective_algebraMap (algebraMap (ZMod p) R).injective p
    have h1 := hFX R ι hx
    have h2 := hFY R (ι ≫ g) (by rw [Category.assoc, hg, hx])
    rw [← Category.assoc, ← h1, Category.assoc, h2, Category.assoc]
  ·
    haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    haveI : IsEmpty ↥(Spec R) := by
      show IsEmpty (PrimeSpectrum R)
      infer_instance
    exact (isInitialOfIsEmpty (X := Spec R)).hom_ext _ _

theorem main (p : ℕ) [Fact p.Prime] {X Y : Scheme.{0}}
    (fX : X ⟶ Spec (CommRingCat.of (ZMod p))) (fY : Y ⟶ Spec (CommRingCat.of (ZMod p)))
    (FX : X ⟶ X) (FY : Y ⟶ Y) (hFXb : FX ≫ fX = fX) (hFYb : FY ≫ fY = fY)
    (hFX : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ FX)
    (hFY : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (y : Spec (CommRingCat.of B) ⟶ Y),
        y ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ y = y ≫ FY)
    (g : X ⟶ Y) (hg : g ≫ fY = fX) :
    FX ≫ g = g ≫ FY :=
  Scheme.Cover.hom_ext X.affineCover _ _ fun j => piece p fX fY FX FY hFX hFY g hg (X.affineCover.f j)

end Ws23.FrobNat

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (p : ℕ) [Fact p.Prime] {X Y : Scheme.{0}}
    (fX : X ⟶ Spec (CommRingCat.of (ZMod p))) (fY : Y ⟶ Spec (CommRingCat.of (ZMod p)))
    (FX : X ⟶ X) (FY : Y ⟶ Y) (hFXb : FX ≫ fX = fX) (hFYb : FY ≫ fY = fY)
    (hFX : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ FX)
    (hFY : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (y : Spec (CommRingCat.of B) ⟶ Y),
        y ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ y = y ≫ FY)
    (g : X ⟶ Y) (hg : g ≫ fY = fX) :
    FX ≫ g = g ≫ FY :=
  Ws23.FrobNat.main p fX fY FX FY hFXb hFYb hFX hFY g hg

end S_AlgebraicGeometry_frobenius_comp_eq_comp_frobenius_of_forall_spec
end P2MW
export P2MW.S_AlgebraicGeometry_frobenius_comp_eq_comp_frobenius_of_forall_spec (solution)
