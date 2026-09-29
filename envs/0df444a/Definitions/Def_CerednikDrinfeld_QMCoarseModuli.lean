-- Prove2me | Definitions.Def_CerednikDrinfeld_QMCoarseModuli
-- name    : CerednikDrinfeld_QMCoarseModuli
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/08294662-7528-5fbc-a5b2-db2fe35164ce
-- title:
--   Coarse moduli schemes for fake elliptic curves with level structure
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ and $N\in\mathbb{N}$, and recall that a `FakeEllipticCurve Λ N S` is a relative two-dimensional abelian scheme over $\operatorname{Spec} S$ with commutative relative group law, an action of $\Lambda$ by endomorphisms with the prescribed trace condition, and a closed subscheme `lev` playing the role of a level-$N$ structure; an `ExtraLevel ℓ` adjoins a further closed subgroup scheme `K` of $\ell$-torsion, finite flat of rank $\ell^2$ over the base, $\Lambda$-stable and meeting `lev` trivially, and `WithExtraLevel Λ N ℓ S` is the type of such pairs.
--
--   The first declaration, `FakeEllipticCurve.WithExtraLevel.IsPullback`, is the base-change relation for these pairs along a ring map $\varphi:S\to S'$: there is a morphism $g$ from the total space of $u'$ to that of $u$ making the square with the two structure morphisms and $\operatorname{Spec}\varphi$ cartesian, such that $g$ transports the relative group law on points, satisfies $u'.\mathrm{act}(x)$ followed by $g$ equals $g$ followed by $u.\mathrm{act}(x)$ for all $x\in\Lambda$, and sends points factoring through the level structure of $u'$, respectively through its extra level, to points factoring through the corresponding structure of $u$ (implications only, not equivalences).
--
--   The two structures `IsCoarseModuli` and `IsCoarseModuliT` are propositions about a base ring $B$, a scheme $X$ (resp. $Y$) with a morphism to $\operatorname{Spec} B$, and a rule `pt` (resp. `ptT`) assigning to every commutative ring $S$, every $B$-scheme structure $s$ on $\operatorname{Spec} S$ and every fake elliptic curve (resp. pair) over $S$ a morphism $\operatorname{Spec} S\to X$ over $s$. The fields assert: invariance of `pt` under the project's isomorphism relation; compatibility with base change, namely that for $\operatorname{Spec}\varphi$ followed by $s$ equal to $s'$ and $E'$ a pullback of $E$ along $\varphi$ the morphism attached to $E'$ is $\operatorname{Spec}\varphi$ followed by that attached to $E$; surjectivity and injectivity on isomorphism classes over every algebraically closed field $k$ with a given $B$-structure; and a universal property, `univ`: for every scheme $T$ over $\operatorname{Spec} B$ and every rule `pt'` into $T$ satisfying the same two naturality clauses, there is a unique $g:X\to T$ over $B$ with $(\mathrm{pt}'\,S\,s\,E)$ equal to $(\mathrm{pt}\,S\,s\,E)$ followed by $g$. `IsCoarseModuliT` is the verbatim analogue for pairs with extra level at $\ell$. No existence of such an $X$ is asserted here.
--
--   **Relation to Mathlib.** Mathlib has no notion of coarse moduli scheme, of abelian surfaces with quaternionic multiplication, or of moduli functors for them; these are the project's own predicates, phrased directly in terms of rules on points rather than through a representability condition on a functor. Mathlib's `CategoryTheory.IsPullback` supplies the cartesian-square condition used in the base-change relation.
--
--   **Where it is used.** These predicates express, for the Čerednik–Drinfeld part of the argument, that a given scheme with a point-rule is the coarse moduli scheme of fake elliptic curves with level-$N$ structure, respectively of such curves together with an extra level subgroup at $\ell$ (the level $\Gamma_0(N)\cap\Gamma^0(\ell)$ presentation used for level raising). The universal property `univ` is what allows two such models to be identified by a unique morphism compatible with the point-rules, so that the moduli description can be transported to the Shimura curve model carrying the Hecke correspondences and Galois action used later.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMCoarseModuli.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion

namespace CerednikDrinfeld.QM

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def FakeEllipticCurve.WithExtraLevel.IsPullback {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {ℓ : ℕ}
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S') : Prop :=
  ∃ (g : u'.1.A ⟶ u.1.A) (hg : CategoryTheory.IsPullback g u'.1.f u.1.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' u'.1.f),
      (u'.1.L.mul t' P Q).1 ≫ g =
        (u.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
    (∀ x : ↥Λ, u'.1.act x ≫ g = g ≫ u.1.act x) ∧
    (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
      (FactorsThrough u'.1.lev P → ∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g) ∧
      (FactorsThrough u'.2.levK P → ∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.1 ≫ g))

structure IsCoarseModuli (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) {B : Type} [CommRing B]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX) : Prop where

  pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (E E' : FakeEllipticCurve Λ N S),
    FakeEllipticCurve.Iso E E' → pt S s E = pt S s E'

  pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
    FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1

  pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s πX),
    ∃ E : FakeEllipticCurve Λ N k, pt k s E = x

  pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))
    (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E'

  univ : ∀ (T : Scheme.{0}) (πT : T ⟶ Spec (CommRingCat.of B))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve Λ N S → SchemeHomOver s πT),
    (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt' S s E = pt' S s E') →
    (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt' S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s E).1) →
    ∃! g : X ⟶ T, g ≫ πT = πX ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (E : FakeEllipticCurve Λ N S),
        (pt' S s E).1 = (pt S s E).1 ≫ g

structure IsCoarseModuliT (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) {B : Type} [CommRing B]
    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of B))
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY) : Prop where

  ptT_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
    FakeEllipticCurve.WithExtraLevel.Iso u u' → ptT S s u = ptT S s u'

  ptT_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
    FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (ptT S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptT S s u).1

  ptT_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B)) (y : SchemeHomOver s πY),
    ∃ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k, ptT k s u = y

  ptT_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))
    (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ k), ptT k s u = ptT k s u' → FakeEllipticCurve.WithExtraLevel.Iso u u'

  univ : ∀ (T : Scheme.{0}) (πT : T ⟶ Spec (CommRingCat.of B))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πT),
    (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
      FakeEllipticCurve.WithExtraLevel.Iso u u' → pt' S s u = pt' S s u') →
    (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
      FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (pt' S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s u).1) →
    ∃! g : Y ⟶ T, g ≫ πT = πY ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (pt' S s u).1 = (ptT S s u).1 ≫ g

end CerednikDrinfeld.QM

end


