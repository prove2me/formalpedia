-- Prove2me | Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
-- name    : ModularCurve_WeierstrassLevelModuliDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/0ec02574-783d-56a3-bb31-f9d119e40bc1
-- title:
--   Rigid Weierstrass level data and their level moduli data
-- statement:
--   Fix a commutative ring $A$. The structure `RigidWeierstrassData A` packages a functor of "rigid" data on Weierstrass curves over commutative $A$-algebras. Its fields are: a family of types `Raw T`, one for each commutative $A$-algebra $T$; an assignment `curve` sending each $x \in$ `Raw T` to a Weierstrass curve over $T$; the requirement `isUnit_Δ` that the discriminant $\Delta$ of `curve x` be a unit, so that the curve is elliptic; a base-change operation `mapRing` along any $A$-algebra homomorphism $f : T \to T'$, compatible with `curve` in the sense that `curve (mapRing f x)` is the Weierstrass curve obtained from `curve x` by applying $f$ coefficientwise, and functorial for the identity and for composition; and an action `act` of the group `WeierstrassCurve.VariableChange T` of Weierstrass changes of variables $(u; r, s, t)$ over $T$ on `Raw T`, with the unit and multiplication laws as fields, inducing the usual action $C \bullet W$ on the underlying curve, and commuting with base change after transporting the change of variables along $f$. Thus the action and functoriality laws are theorems carried as data.
--
--   For such an $R$, `Rel` is the relation on `Raw T` given by $x \sim y$ iff $y =$ `act C x` for some change of variables $C$; it is recorded as reflexive (`Rel.refl`) and transitive (`Rel.trans`), and `Pt T` is the quotient of `Raw T` by `Rel` formed with `Quot`, i.e. by the orbit relation of the variable-change action. The map `map f` descends base change to these quotients, and `jOf` descends the $j$-invariant: on a representative $x$ it is the $j$-invariant of `curve x`, which is well defined because $j$ is unchanged by a change of variables. The lemmas `map_mk` and `jOf_mk` record the values on representatives, and `smul_curve_eq` restates associativity of the variable-change action on Weierstrass curves. Finally, `toLevelModuliDatum` assembles $T \mapsto$ `Pt T`, together with `map` and `jOf`, into a `LevelModuliDatum A`: a functor from commutative $A$-algebras and $A$-algebra maps to types, equipped with a $j$-coordinate function commuting with the structure maps.
--
--   **Relation to Mathlib.** Mathlib supplies `WeierstrassCurve`, its `VariableChange` group with the action $C \bullet W$, base change along a ring homomorphism, and the $j$-invariant of an elliptic curve; the notions of rigid Weierstrass level datum and of level moduli datum are the project's own, built on these.
--
--   **Where it is used.** This is the generic passage from a rigid level structure on Weierstrass curves — a cyclic subgroup of order $N$, a basis of the $\ell$-torsion, a Drinfeld basis in characteristic $q$ — to a moduli problem in the form of a `LevelModuliDatum`, by quotienting out Weierstrass isomorphisms. It lets the statement that a chart algebra of an integral model of a modular curve represents the corresponding moduli problem, with prescribed $j$-coordinate, be formulated uniformly for the level structures used in the modularity and level-lowering arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_WeierstrassLevelModuliDatum.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace ModularCurve

structure RigidWeierstrassData (A : Type u) [CommRing A] where

  Raw : (T : Type u) → [CommRing T] → [Algebra A T] → Type u

  curve : {T : Type u} → [CommRing T] → [Algebra A T] → Raw T → WeierstrassCurve T

  isUnit_Δ : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : Raw T), IsUnit (curve x).Δ

  mapRing : {T T' : Type u} → [CommRing T] → [Algebra A T] → [CommRing T'] → [Algebra A T'] →
    (T →ₐ[A] T') → Raw T → Raw T'

  curve_mapRing : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : Raw T), curve (mapRing f x) = (curve x).map f.toRingHom

  mapRing_id : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : Raw T), mapRing (AlgHom.id A T) x = x

  mapRing_comp : ∀ {T T' T'' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing T'']
    [Algebra A T''] (f : T →ₐ[A] T') (g : T' →ₐ[A] T'') (x : Raw T), mapRing (g.comp f) x = mapRing g (mapRing f x)

  act : {T : Type u} → [CommRing T] → [Algebra A T] → WeierstrassCurve.VariableChange T → Raw T → Raw T

  act_one : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : Raw T), act (1 : WeierstrassCurve.VariableChange T) x = x

  act_mul : ∀ {T : Type u} [CommRing T] [Algebra A T] (C C' : WeierstrassCurve.VariableChange T) (x : Raw T),
    act (C * C') x = act C (act C' x)

  curve_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T) (x : Raw T),
    curve (act C x) = C • curve x

  mapRing_act : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (C : WeierstrassCurve.VariableChange T) (x : Raw T),
    mapRing f (act C x) = act (C.map f.toRingHom) (mapRing f x)

namespace RigidWeierstrassData

variable {A : Type u} [CommRing A] (R : RigidWeierstrassData.{u} A)

def Rel {T : Type u} [CommRing T] [Algebra A T] (x y : R.Raw T) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange T, y = R.act C x

theorem Rel.refl {T : Type u} [CommRing T] [Algebra A T] (x : R.Raw T) : R.Rel x x := ⟨1, (R.act_one x).symm⟩

theorem Rel.trans {T : Type u} [CommRing T] [Algebra A T] {x y z : R.Raw T} (h : R.Rel x y) (h' : R.Rel y z) :
    R.Rel x z := by
  obtain ⟨C, rfl⟩ := h; obtain ⟨C', rfl⟩ := h'
  exact ⟨C' * C, (R.act_mul C' C x).symm⟩

theorem smul_curve_eq (T : Type u) [CommRing T] (C C' : WeierstrassCurve.VariableChange T) (W : WeierstrassCurve T) :
    (C * C') • W = C • (C' • W) := mul_smul C C' W

def Pt (T : Type u) [CommRing T] [Algebra A T] : Type u := Quot (R.Rel (T := T))

def map {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') :
    R.Pt T → R.Pt T' :=
  Quot.lift (fun x => Quot.mk _ (R.mapRing f x)) (by
    rintro x y ⟨C, rfl⟩
    exact Quot.sound ⟨C.map f.toRingHom, R.mapRing_act f C x⟩)

theorem map_mk {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : R.Raw T) : R.map f (Quot.mk _ x) = Quot.mk _ (R.mapRing f x) := rfl

noncomputable def jOf {T : Type u} [CommRing T] [Algebra A T] : R.Pt T → T :=
  Quot.lift (fun x => (R.curve x).jOfUnit (R.isUnit_Δ x)) (by
    rintro x y ⟨C, rfl⟩
    show (R.curve x).jOfUnit (R.isUnit_Δ x) = (R.curve (R.act C x)).jOfUnit (R.isUnit_Δ (R.act C x))
    have key : ∀ (W' : WeierstrassCurve T) (hW' : IsUnit W'.Δ) (hEq : W' = C • R.curve x),
        W'.jOfUnit hW' = (R.curve x).jOfUnit (R.isUnit_Δ x) := by
      intro W' hW' hEq
      subst hEq
      exact (R.curve x).jOfUnit_variableChange C (R.isUnit_Δ x) hW'
    exact (key _ _ (R.curve_act C x)).symm)

theorem jOf_mk {T : Type u} [CommRing T] [Algebra A T] (x : R.Raw T) :
    R.jOf (Quot.mk _ x) = (R.curve x).jOfUnit (R.isUnit_Δ x) := rfl

noncomputable def toLevelModuliDatum : LevelModuliDatum.{u} A where
  Pt := fun T _ _ => R.Pt T
  map := fun f => R.map f
  map_id := by
    intro T _ _ x
    induction x using Quot.ind with
    | mk x => rw [map_mk, R.mapRing_id]
  map_comp := by
    intro T T' T'' _ _ _ _ _ _ f g x
    induction x using Quot.ind with
    | mk x => rw [map_mk, map_mk, map_mk, R.mapRing_comp]
  jOf := fun x => R.jOf x
  jOf_map := by
    intro T T' _ _ _ _ f x
    induction x using Quot.ind with
    | mk x =>
      rw [map_mk, jOf_mk, jOf_mk]
      have key : ∀ (W' : WeierstrassCurve T') (hW' : IsUnit W'.Δ) (hEq : W' = (R.curve x).map f.toRingHom),
          W'.jOfUnit hW' = f ((R.curve x).jOfUnit (R.isUnit_Δ x)) := by
        intro W' hW' hEq
        subst hEq
        exact (R.curve x).jOfUnit_map f.toRingHom (R.isUnit_Δ x) hW'
      exact key _ _ (R.curve_mapRing f x)

end RigidWeierstrassData

end ModularCurve


