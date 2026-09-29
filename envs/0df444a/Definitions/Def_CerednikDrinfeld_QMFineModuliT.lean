-- Prove2me | Definitions.Def_CerednikDrinfeld_QMFineModuliT
-- name    : CerednikDrinfeld_QMFineModuliT
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/96aec9fe-062a-5e1e-8139-56949897638a
-- title:
--   Fine moduli of fake elliptic curves with extra level
-- statement:
--   Throughout, $\Lambda$ is a $\mathbb{Z}$-submodule of a rational quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and `WithFullLevel Λ N n S` denotes a pair $u=(E,P)$ consisting of a fake elliptic curve $E$ over $S$ with $\Gamma_0(N)$-type level subscheme `E.lev` and an $\Lambda$-action, together with a full level-$n$ structure: a section $P$ killed by $n$ whose $\Lambda$-orbit exhausts the geometric $n$-torsion and whose annihilator in $\Lambda$ is $n\Lambda$. The first group of declarations makes the existential witness of the relations `WithFullLevel.Iso` and `WithFullLevel.IsTwist` explicit. For an isomorphism of schemes $i : E \cong E'$ with $i \circ$ (structure map of $E'$) $=$ structure map of $E$, `IsoVia u u' i hi` asserts: $i$ is compatible with the relative group laws on all $T$-points over $S$; $i$ intertwines the two $\Lambda$-actions; a $T$-point factors through `E.lev` if and only if its image factors through `E'.lev`; and $i$ carries $P$ to $P'$. `IsTwistVia c u u' e he` has the same first three clauses but requires $e$ to carry $c\cdot P$ to $P'$, for $c\in\Lambda$. The two lemmas `iff_exists_via` state that `Iso` (resp. `IsTwist`) holds exactly when such a witness exists. `IsoTVia u u' C C' i hi` adds to `IsoVia` that, for extra level-$\ell$ data $C$ on $E$ and $C'$ on $E'$, a $T$-point factors through `C.levK` iff its image factors through `C'.levK`.
--
--   The structure `IsFineModuliT Λ N n ℓ Mℓ πMℓ ptFℓ` is a four-field predicate on a scheme $M_\ell$ over $\operatorname{Spec} B$ together with a rule $\mathrm{ptF}_\ell$ assigning to each $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and each triple $(u,C)$ a point of $M_\ell$ over $s$: the value depends only on the `IsoTVia`-class; it is compatible with base change along a ring map $\varphi : S \to S'$ with $\operatorname{Spec}\varphi$ followed by $s$ equal to $s'$, where the base-change relation is witnessed by a single morphism $g : E' \to E$ exhibiting `IsPullbackVia φ` (cartesian square, compatibility with group laws, $\Lambda$-equivariance, and transport of the $\Gamma_0(N)$-structure) which moreover carries $P'$ to the pullback of $P$ and carries $C'$ into $C$; the rule is surjective onto the points of $M_\ell$ over every $s$; and it is injective up to `IsoTVia`. Everything is at universe $0$.
--
--   **Relation to Mathlib.** Mathlib has no notion of fake elliptic curve, of level structures on one, or of a representability predicate for such moduli problems; these are the project's own, formulated directly in terms of $T$-points and relative group laws. `IsFineModuliT` is the extra-level-$\ell$ counterpart of the project's `IsFineModuli`.
--
--   **Where it is used.** These predicates specify the integral models of Shimura curves attached to an indefinite rational quaternion algebra as fine moduli schemes of fake elliptic curves with full level $n$ and an additional level-$\ell$ structure, the setting in which the Čerednik–Drinfel'd uniformisation and the resulting local description of the Jacobian are formulated. The named-witness forms are what consumers bind in order to state the level-twisting action of a group on $M_\ell$, since automorphisms of the curve move the extra level data and the twisting map must be the one fixed by the twist of $P$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMFineModuliT.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace CerednikDrinfeld.QM

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def WithFullLevel.IsoVia {S : Type} [CommRing S] {n : ℕ} (u u' : WithFullLevel Λ N n S)
    (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) : Prop :=
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt i.hom hi (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt i.hom hi P) (mapPt i.hom hi Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ i.hom = i.hom ≫ u'.1.act x) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt i.hom hi P)) ∧
    mapPt i.hom hi u.2.P = u'.2.P

theorem WithFullLevel.iso_iff_exists_via {S : Type} [CommRing S] {n : ℕ} (u u' : WithFullLevel Λ N n S) :
    WithFullLevel.Iso u u' ↔ ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), WithFullLevel.IsoVia u u' i hi := Iff.rfl

def WithFullLevel.IsTwistVia {S : Type} [CommRing S] {n : ℕ} (c : ↥Λ) (u u' : WithFullLevel Λ N n S)
    (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f) : Prop :=
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u'.1.act x) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt e.hom he P)) ∧
    mapPt e.hom he (pushPt (u.1.act c) (u.1.act_over c) u.2.P) = u'.2.P

theorem WithFullLevel.isTwist_iff_exists_via {S : Type} [CommRing S] {n : ℕ} (c : ↥Λ) (u u' : WithFullLevel Λ N n S) :
    WithFullLevel.IsTwist c u u' ↔ ∃ (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f), WithFullLevel.IsTwistVia c u u' e he :=
  Iff.rfl

def WithFullLevel.IsoTVia {S : Type} [CommRing S] {n ℓ : ℕ} (u u' : WithFullLevel Λ N n S)
    (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ) (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) : Prop :=
  WithFullLevel.IsoVia u u' i hi ∧
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough C.levK P ↔ FactorsThrough C'.levK (mapPt i.hom hi P)

end FakeEllipticCurve

variable {a b : ℚ}

structure IsFineModuliT (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N n ℓ : ℕ) {B : Type} [CommRing B]
    (Mℓ : Scheme.{0}) (πMℓ : Mℓ ⟶ Spec (CommRingCat.of B))
    (ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S), u.1.ExtraLevel ℓ → SchemeHomOver s πMℓ) : Prop where

  ptFℓ_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ)
    (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f),
    FakeEllipticCurve.WithFullLevel.IsoTVia u u' C C' i hi → ptFℓ S s u C = ptFℓ S s u' C'

  ptFℓ_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
      (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ) (g : u'.1.A ⟶ u.1.A),
      FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 g →
      (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1 →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t u'.1.f),
        FactorsThrough C'.levK P → ∃ P₀ : T ⟶ C.K, P₀ ≫ C.levK = P.1 ≫ g) →
        (ptFℓ S' s' u' C').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptFℓ S s u C).1

  ptFℓ_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s πMℓ),
    ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ), ptFℓ S s u C = x

  ptFℓ_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ),
    ptFℓ S s u C = ptFℓ S s u' C' →
      ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia u u' C C' i hi

end CerednikDrinfeld.QM


