-- Prove2me | Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctorRestrict
-- name    : WeierstrassCurve_DrinfeldLevelFunctorRestrict
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/77ebeaa2-0aca-595e-a528-dcedd4c3befc
-- title:
--   Restriction of scalars for group laws and level transports
-- statement:
--   Fix a commutative ring $A_0$, an $A_0$-algebra $A$, and a natural number $q$. The module records how the two pieces of data indexed by a base ring in the Drinfeld-level moduli package — a guarded family of group laws and a transport of Drinfeld pairs — are re-read over $A$ when they are given over $A_0$.
--
--   `algebraRestrict A₀ A T` is the $A_0$-algebra structure on an $A$-algebra $T$ whose structure map is $A_0 \to A$ followed by $A \to T$; `isScalarTower_algebraRestrict` states that $A_0$, $A$, $T$ then form a scalar tower. `algHomRestrict` sends an $A$-algebra map $f : T \to T'$ to the $A_0$-algebra map with the same underlying ring homomorphism, and `algHomRestrict_toRingHom`, `algHomRestrict_id`, `algHomRestrict_comp` record that this preserves underlying ring maps, identities and composites.
--
--   Here `GroupLaws A` is the type of families assigning, to every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with $\Delta_W$ a unit, a group law on the functor of $T$-scheme points of the $\mathrm{Proj}$ model of $W$. `GroupLaws.restrictScalars A 𝒢₀` is the family over $A$ whose value on $(T, W, h_\Delta)$ is the value of $\mathcal G_0$ on $T$ equipped with the composite $A_0$-algebra structure; `GroupLaws.restrictScalars_apply` states this pointwise. Similarly `LevelTransport A₀ 𝒢₀ q` is a structure carrying a transport of raw Drinfeld pairs (a curve together with two sections of its $\mathrm{Proj}$ model) along algebra maps and along Weierstrass variable changes, whose fields are the functoriality and equivariance laws together with the preservation of the level predicate `RawDrinfeldPair.IsLevel`. `LevelTransport.restrictScalars` produces a `LevelTransport A (𝒢₀.restrictScalars A) q` whose transport along an $A$-algebra map $f$ is the transport of $\mathcal T_0$ along `algHomRestrict A₀ A f`, and whose variable-change action is that of $\mathcal T_0$; the two final lemmas state these two descriptions, and all structure fields are the corresponding laws for $\mathcal T_0$.
--
--   **Relation to Mathlib.** The composite algebra structure is Mathlib's `RingHom.toAlgebra` applied to the composite of the two structure maps; `algHomRestrict` plays, for that structure, the role of Mathlib's restriction of scalars for algebra maps. `GroupLaws`, `LevelTransport` and the raw Drinfeld pairs they act on are the project's own notions, Mathlib having no relative group law on `Proj` models of Weierstrass curves nor Drinfeld level structures.
--
--   **Where it is used.** Together with the level components for $\Gamma_0(N)$ and for level $p$, a guarded group-law family and a level transport assemble into the rigidified Weierstrass moduli datum with full level $q$ structure. The restriction constructions here let such a datum, constructed once over a base ring $A_0$, be used over any $A_0$-algebra $A$, as required when the moduli data are specialised to the coefficient rings occurring in the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_DrinfeldLevelFunctorRestrict.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel

namespace WeierstrassCurve.DrinfeldGlobal

@[reducible] def algebraRestrict (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    (T : Type u) [CommRing T] [Algebra A T] : Algebra A₀ T :=
  ((algebraMap A T).comp (algebraMap A₀ A)).toAlgebra

theorem isScalarTower_algebraRestrict (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    (T : Type u) [CommRing T] [Algebra A T] :
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    IsScalarTower A₀ A T :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def GroupLaws.restrictScalars {A₀ : Type u} [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (𝒢₀ : GroupLaws A₀) :
    GroupLaws A :=
  fun T _ _ W hΔ =>
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    𝒢₀ T W hΔ

theorem GroupLaws.restrictScalars_apply {A₀ : Type u} [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (𝒢₀ : GroupLaws A₀)
    (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ) :
    𝒢₀.restrictScalars A T W hΔ = (letI : Algebra A₀ T := algebraRestrict A₀ A T; 𝒢₀ T W hΔ) :=
  rfl

def algHomRestrict (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') :
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    T →ₐ[A₀] T' :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  letI : Algebra A₀ T' := algebraRestrict A₀ A T'
  { toRingHom := f.toRingHom
    commutes' := fun a => by
      show f (algebraMap A T (algebraMap A₀ A a)) = algebraMap A T' (algebraMap A₀ A a)
      exact f.commutes _ }

theorem algHomRestrict_toRingHom (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') :
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    (algHomRestrict A₀ A f).toRingHom = f.toRingHom :=
  rfl

theorem algHomRestrict_id (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (T : Type u) [CommRing T] [Algebra A T] :
    algHomRestrict A₀ A (AlgHom.id A T) = (letI : Algebra A₀ T := algebraRestrict A₀ A T; AlgHom.id A₀ T) :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  AlgHom.ext fun _ => rfl

theorem algHomRestrict_comp (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    {T T' T'' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing T''] [Algebra A T'']
    (f : T →ₐ[A] T') (g : T' →ₐ[A] T'') :
    algHomRestrict A₀ A (g.comp f) =
      (letI : Algebra A₀ T := algebraRestrict A₀ A T
       letI : Algebra A₀ T' := algebraRestrict A₀ A T'
       letI : Algebra A₀ T'' := algebraRestrict A₀ A T''
       (algHomRestrict A₀ A g).comp (algHomRestrict A₀ A f)) :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  letI : Algebra A₀ T' := algebraRestrict A₀ A T'
  letI : Algebra A₀ T'' := algebraRestrict A₀ A T''
  AlgHom.ext fun _ => rfl

def LevelTransport.restrictScalars {A₀ : Type u} [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    {𝒢₀ : GroupLaws A₀} {q : ℕ}
    (𝒯₀ : LevelTransport A₀ 𝒢₀ q) : LevelTransport A (𝒢₀.restrictScalars A) q where
  map {T T'} _ _ _ _ f x :=
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    𝒯₀.map (algHomRestrict A₀ A f) x
  act {T} _ _ C x :=
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    𝒯₀.act C x
  map_id {T} _ _ x := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    show 𝒯₀.map (algHomRestrict A₀ A (AlgHom.id A T)) x = x
    rw [algHomRestrict_id]
    exact 𝒯₀.map_id x
  map_comp {T T' T''} _ _ _ _ _ _ f g x := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    letI : Algebra A₀ T'' := algebraRestrict A₀ A T''
    show 𝒯₀.map (algHomRestrict A₀ A (g.comp f)) x = 𝒯₀.map (algHomRestrict A₀ A g) (𝒯₀.map (algHomRestrict A₀ A f) x)
    rw [algHomRestrict_comp]
    exact 𝒯₀.map_comp _ _ x
  act_one {T} _ _ x := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    exact 𝒯₀.act_one x
  act_mul {T} _ _ C C' x := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    exact 𝒯₀.act_mul C C' x
  map_act {T T'} _ _ _ _ f C x := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    exact 𝒯₀.map_act (algHomRestrict A₀ A f) C x
  isLevel_map {T T'} _ _ _ _ f W x h := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    exact 𝒯₀.isLevel_map (algHomRestrict A₀ A f) W x h
  isLevel_act {T} _ _ C W x h := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    exact 𝒯₀.isLevel_act C W x h

theorem LevelTransport.restrictScalars_map {A₀ : Type u} [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    {𝒢₀ : GroupLaws A₀} {q : ℕ}
    (𝒯₀ : LevelTransport A₀ 𝒢₀ q)
    {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') (x : RawDrinfeldPair T) :
    (𝒯₀.restrictScalars A).map f x =
      (letI : Algebra A₀ T := algebraRestrict A₀ A T
       letI : Algebra A₀ T' := algebraRestrict A₀ A T'
       𝒯₀.map (algHomRestrict A₀ A f) x) :=
  rfl

theorem LevelTransport.restrictScalars_act {A₀ : Type u} [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    {𝒢₀ : GroupLaws A₀} {q : ℕ}
    (𝒯₀ : LevelTransport A₀ 𝒢₀ q)
    {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T) (x : RawDrinfeldPair T) :
    (𝒯₀.restrictScalars A).act C x = (letI : Algebra A₀ T := algebraRestrict A₀ A T; 𝒯₀.act C x) :=
  rfl

end WeierstrassCurve.DrinfeldGlobal

end


