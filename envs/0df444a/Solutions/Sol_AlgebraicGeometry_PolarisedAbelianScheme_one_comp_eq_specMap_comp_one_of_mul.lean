-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.one_comp_eq_specMap_comp_one_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/36915afc-422b-50e5-8c4e-0b6e6dc56c8a

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_one_comp_eq_specMap_comp_one_of_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

namespace BenchR_EDd

universe u

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem eq_one_of_mul_self (L : RelativeGroupLaw S f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f) (hx : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.one t := by rw [hx, L.inv_mul_cancel]

theorem schemeHomOverComp_one (L : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (L.one t) = L.one t' := by
  apply eq_one_of_mul_self
  have := L.mul_natural t t' ψ hψ (L.one t) (L.one t)
  rw [L.one_mul] at this
  exact this.symm

end BenchR_EDd

open BenchR_EDd in
theorem solution
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
    (gA : u'.A ⟶ u.A) (hg : CategoryTheory.IsPullback gA u'.f u.f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' u'.f),
      (u'.L.mul t' x y).1 ≫ gA =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) :
    (u'.L.one (𝟙 _)).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (u.L.one (𝟙 _)).1 := by

  set x : SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom φ)) u.f :=
    ⟨(u'.L.one (𝟙 _)).1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, (u'.L.one (𝟙 _)).2]⟩ with hxdef
  have key := hmul (𝟙 _) (u'.L.one (𝟙 _)) (u'.L.one (𝟙 _))
  rw [u'.L.one_mul] at key

  have hx : u.L.mul _ x x = x := Subtype.ext key.symm
  have h1 : x = u.L.one _ := eq_one_of_mul_self u.L _ x hx

  have hψ : Spec.map (CommRingCat.ofHom φ) ≫ 𝟙 (Spec (CommRingCat.of S)) =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom φ) := by simp
  have h2 := schemeHomOverComp_one u.L (𝟙 _) (𝟙 _ ≫ Spec.map (CommRingCat.ofHom φ))
    (Spec.map (CommRingCat.ofHom φ)) hψ
  have h3 : x.1 = (schemeHomOverComp (Spec.map (CommRingCat.ofHom φ)) hψ (u.L.one (𝟙 _))).1 := by
    rw [h2, h1]
  simpa [schemeHomOverComp] using h3

end S_AlgebraicGeometry_PolarisedAbelianScheme_one_comp_eq_specMap_comp_one_of_mul
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_one_comp_eq_specMap_comp_one_of_mul (solution)
