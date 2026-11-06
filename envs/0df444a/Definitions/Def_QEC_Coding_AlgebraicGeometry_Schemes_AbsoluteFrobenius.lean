-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
-- name    : QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:51:09.869908+00:00
-- url     : https://prove2.me/theorems/a7d9c1a9-efc3-48a0-b752-e0810483ff5b
-- title:
--   Absolute Frobenius
-- statement:
--   Definitions and structural lemmas for Absolute Frobenius, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/AbsoluteFrobenius.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Geometry.RingedSpace.Stalks
set_option autoImplicit false
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
open QEC.Coding.AlgebraicGeometry.PrimeFrobenius
variable (p : ℕ) [Fact p.Prime] (X : Scheme) (f : X ⟶ Spec (.of (ZMod p)))
def sectionBase (U : X.Opens) : ZMod p →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of (ZMod p))).inv ≫ f.appTop ≫
    X.presheaf.map (homOfLE le_top).op).hom
def sectionPower (U : X.Opens) : Γ(X, U) →+* Γ(X, U) :=
  letI : Algebra (ZMod p) Γ(X, U) := (sectionBase p X f U).toAlgebra
  primeAlgebraFrobenius p Γ(X, U)
abbrev powerPresheafHom : X.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := 𝟙 X.toTopCat
  c := {
    app := fun U => CommRingCat.ofHom (sectionPower p X f U.unop)
    naturality := by
      intro U V i
      ext s
      change (X.presheaf.map i s)^p = X.presheaf.map i (s^p)
      exact ((X.presheaf.map i).hom.map_pow s p).symm
  }
lemma powerPresheafHom_stalk_apply (x : X) (s : X.presheaf.stalk x) :
    (powerPresheafHom p X f).stalkMap x s = s^p := by
  obtain ⟨U, hx, a, rfl⟩ := X.presheaf.exists_germ_eq s
  have hg := PresheafedSpace.stalkMap_germ_apply (powerPresheafHom p X f) U x hx a
  change (powerPresheafHom p X f).stalkMap x (X.presheaf.germ U x hx a) =
    X.presheaf.germ U x hx (a^p) at hg
  exact hg.trans ((X.presheaf.germ U x hx).hom.map_pow a p)
def absoluteFrobenius : X ⟶ X := Scheme.Hom.mk {
  toHom := powerPresheafHom p X f
  prop := by
    intro x
    constructor
    intro a ha
    have hpow := powerPresheafHom_stalk_apply p X f x a
    change ((powerPresheafHom p X f).stalkMap x).hom a = a^p at hpow
    rw [hpow] at ha
    exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp ha
}
end
end QEC.Coding.AlgebraicGeometry.SchemeFrobenius


