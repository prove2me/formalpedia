-- Prove2me | Definitions.Def_CerednikDrinfeld_QMFineModuli
-- name    : CerednikDrinfeld_QMFineModuli
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/617b24af-7ade-512c-8320-8b046f511b8e
-- title:
--   Full level structures on fake elliptic curves; fine moduli
-- statement:
--   Throughout, $a,b\in\mathbb Q$, $\Lambda$ is a $\mathbb Z$-submodule of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, $N$ is a natural number, and a fake elliptic curve $E$ over a commutative ring $S$ is the project's structure `FakeEllipticCurve Λ N S`: a scheme $A\to\operatorname{Spec}S$ with a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, a multiplicative action $x\mapsto E.\mathrm{act}\,x$ of $\Lambda$ by endomorphisms over the base satisfying a trace condition, and a closed level subscheme $E.\mathrm{lev}:C\to A$ of relative rank $N^2$. For such an $E$ and $m:\mathbb N$, `FullLevel E m` carries one datum, a section $P$ of $E.f$ over $\operatorname{Spec}S$, and three conditions: $m\cdot P$ is the identity section; for every algebraically closed field $k$, every ring map $S\to k$ and every $k$-point $Q$ of the fibre with $m\cdot Q=0$ there is $x\in\Lambda$ with $E.\mathrm{act}(x)$ applied to the restriction of $P$ equal to $Q$; and, for $x\in\Lambda$, $E.\mathrm{act}(x)$ applied to that restriction is the identity exactly when $x\in m\Lambda$. Thus $x\mapsto E.\mathrm{act}(x)P$ induces, on every geometric fibre, a bijection of $\Lambda/m\Lambda$ onto the $m$-torsion; no invertibility of $m$ is required. `WithFullLevel Λ N m S` is the type of pairs $u=(E,P)$. Three relations on such pairs are defined by exhibiting a morphism with properties: `Iso` (an isomorphism of the total spaces over the base respecting the group law and the $\Lambda$-action, matching the conditions of factoring through the level subschemes, and carrying $P$ to $P'$); `IsTwist c` (the same, with the last condition replaced by: the morphism carries $E.\mathrm{act}(c)P$ to $P'$); and `IsPullback φ` for a ring map $\varphi:S\to S'$ (a cartesian square over $\operatorname{Spec}\varphi$, compatible with group law and $\Lambda$-action, sending points factoring through the level subscheme of $u'$ to points factoring through that of $u$, and sending $P'$ to the base change of $P$). A helper `sectionAt` restricts a section over $\operatorname{Spec}S$ along a geometric point.
--
--   `IsFineModuli Λ N m M πM ptF` is a predicate on a scheme $M$ over $\operatorname{Spec}B$ together with a rule $\mathrm{ptF}$ assigning to each commutative ring $S$, each morphism $s:\operatorname{Spec}S\to\operatorname{Spec}B$ and each $u\in$ `WithFullLevel Λ N m S` a point of $M$ over $s$. Its four fields say: $\mathrm{ptF}$ is constant on `Iso`-classes; it is compatible with base change along ring maps in the sense of `IsPullback`; for every $S$ and $s$ it is surjective onto the points of $M$ over $s$; and it is injective up to `Iso`. So $M$ represents the functor of isomorphism classes over arbitrary $B$-algebras, in contrast with the coarse version, where bijectivity is demanded only over algebraically closed fields and supplemented by a universal property. `IsLevelTwistAction` adds a group $G$, a homomorphism $\rho:G\to\operatorname{Aut}M$ and a map $\chi:G\to\Lambda$, and asserts: each $\rho(g)$ is over the base; if $u'$ is the $\chi(g)$-twist of $u$ then $\mathrm{ptF}(u')$ is $\mathrm{ptF}(u)$ followed by $\rho(g)$; $\chi(1)\equiv 1$ and $\chi(gg')\equiv\chi(g)\chi(g')$ modulo $m\Lambda$; every $c\in\Lambda$ admitting a two-sided inverse modulo $m\Lambda$ is congruent to some $\chi(g)$; and $\chi$ is injective modulo $m\Lambda$. Together these identify $G$ with the units of $\Lambda/m\Lambda$ acting on $M$ by twisting the full level structure.
--
--   **Relation to Mathlib.** Mathlib has no fake elliptic curves, quaternionic multiplication on abelian schemes, or moduli problems for them; these are the project's own notions, formulated with Mathlib's schemes, morphism properties and `CategoryTheory.Aut`, and with the relative group law and the functor of points over a base morphism supplied by other modules of the project.
--
--   **Where it is used.** These definitions set up the moduli description of the Shimura curves attached to an indefinite quaternion algebra over $\mathbb Q$: a fine moduli scheme for fake elliptic curves with full level $m$ carries an action of the units of $\Lambda/m\Lambda$ by twisting, and the associated coarse moduli scheme is obtained as the quotient. That integral model, and its reduction behaviour, underlie the Čerednik–Drinfeld comparison used to transfer Galois representations between Shimura curves and modular curves in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMFineModuli.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion

namespace CerednikDrinfeld.QM

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def sectionAt {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) (k : Type u) [Field k] (sk : S →+* k) :
    SchemeHomOver (geomPoint k sk) f :=
  schemeHomOverComp (geomPoint k sk) (Category.comp_id _) P

structure FullLevel {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) (m : ℕ) : Type u where

  P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f

  torsion : nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m P = E.L.one (𝟙 (Spec (CommRingCat.of S)))

  generates : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
    nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk) →
      ∃ x : ↥Λ, pushPt (E.act x) (E.act_over x) (sectionAt P k sk) = Q

  annihilator : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (x : ↥Λ),
    pushPt (E.act x) (E.act_over x) (sectionAt P k sk) = E.L.one (geomPoint k sk) ↔
      ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])

abbrev WithFullLevel (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ) (S : Type u) [CommRing S] : Type (u + 1) :=
  Σ E : FakeEllipticCurve Λ N S, E.FullLevel m

def WithFullLevel.Iso {S : Type u} [CommRing S] {m : ℕ} (u u' : WithFullLevel Λ N m S) : Prop :=
  ∃ (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u'.1.act x) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt e.hom he P)) ∧
    mapPt e.hom he u.2.P = u'.2.P

def WithFullLevel.IsTwist {S : Type u} [CommRing S] {m : ℕ} (c : ↥Λ) (u u' : WithFullLevel Λ N m S) : Prop :=
  ∃ (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u'.1.act x) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt e.hom he P)) ∧
    mapPt e.hom he (pushPt (u.1.act c) (u.1.act_over c) u.2.P) = u'.2.P

def WithFullLevel.IsPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') {m : ℕ}
    (u : WithFullLevel Λ N m S) (u' : WithFullLevel Λ N m S') : Prop :=
  ∃ (g : u'.1.A ⟶ u.1.A) (hg : CategoryTheory.IsPullback g u'.1.f u.1.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' u'.1.f),
      (u'.1.L.mul t' P Q).1 ≫ g =
        (u.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
    (∀ x : ↥Λ, u'.1.act x ≫ g = g ≫ u.1.act x) ∧
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
      FactorsThrough u'.1.lev P → ∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g) ∧
    (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1

end FakeEllipticCurve

variable {a b : ℚ}

structure IsFineModuli (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ) {B : Type} [CommRing B]
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of B))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM) : Prop where

  ptF_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S), FakeEllipticCurve.WithFullLevel.Iso u u' → ptF S s u = ptF S s u'

  ptF_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u' : FakeEllipticCurve.WithFullLevel Λ N m S'),
    FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → (ptF S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptF S s u).1

  ptF_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s πM),
    ∃ u : FakeEllipticCurve.WithFullLevel Λ N m S, ptF S s u = x

  ptF_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S), ptF S s u = ptF S s u' → FakeEllipticCurve.WithFullLevel.Iso u u'

structure IsLevelTwistAction (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ) {B : Type} [CommRing B]
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of B))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) : Prop where

  over_base : ∀ g : G, (ρ g).hom ≫ πM = πM

  twist : ∀ (g : G) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S),
    FakeEllipticCurve.WithFullLevel.IsTwist (χ g) u u' → (ptF S s u').1 = (ptF S s u).1 ≫ (ρ g).hom

  label_one : ∃ y : ↥Λ, (χ 1 : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])

  label_mul : ∀ g g' : G,
    ∃ y : ↥Λ, (χ (g * g') : ℍ[ℚ, a, b]) - (χ g : ℍ[ℚ, a, b]) * (χ g' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])

  label_surjective : ∀ c d : ↥Λ,
    (∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) →
    (∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) →
      ∃ (g : G) (y : ↥Λ), (χ g : ℍ[ℚ, a, b]) - (c : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])

  label_injective : ∀ g g' : G,
    (∃ y : ↥Λ, (χ g : ℍ[ℚ, a, b]) - (χ g' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) → g = g'

end CerednikDrinfeld.QM

end


