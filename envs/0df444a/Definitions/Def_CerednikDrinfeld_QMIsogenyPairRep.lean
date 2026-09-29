-- Prove2me | Definitions.Def_CerednikDrinfeld_QMIsogenyPairRep
-- name    : CerednikDrinfeld_QMIsogenyPairRep
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/29d13c5c-faca-5a7c-9741-6f39d2a7fceb
-- title:
--   Point rules representing fixed-degree isogeny pairs of fake elliptic curves
-- statement:
--   Throughout, $\Lambda$ is a $\mathbb{Z}$-lattice in a rational quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, $N$ a level, and `FakeEllipticCurve Λ N S` the project's notion of a fake elliptic curve over a commutative ring $S$: a smooth proper scheme with connected fibres and a relative commutative group law, fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms compatible with the group law and additive in the acting element and with the prescribed reduced trace on tangent spaces, together with a closed immersion `lev` cutting out a finite flat level subscheme of rank $N^2$ with geometric fibres isomorphic to $(\mathbb{Z}/N)^2$.
--
--   Given $r,d$, fake elliptic curves $E,A$ over $S$ and a morphism $\xi : X \to \operatorname{Spec} S$, the type `PtFamily r d E A ξ` consists of the rules assigning a point of $X(T)$ over $\operatorname{Spec} S$ — that is, an element of `SchemeHomOver (Spec.map (algebraMap S T)) ξ` — to each $S$-algebra $T$, each choice of models $E', A'$ over $T$ together with comparison maps $g_E, g_A$ exhibiting them as pullbacks of $E$ and $A$ in the sense of `IsPullbackVia` (a cartesian square compatible with the group laws, $\Lambda$-equivariant, and carrying level points to level points), and each pair $(\varphi : E' \to A', \varphi' : A' \to E')$ over the base with `IsIsogenyPair (r ^ d)` — both maps group-law homomorphisms commuting with the $\Lambda$-actions, with $\varphi\varphi'$ and $\varphi'\varphi$ equal to the action of $r^d$ whenever that scalar lies in $\Lambda$ — and with `PreservesLevel`, i.e. $\varphi$ sends points factoring through the level subscheme of $E'$ to points factoring through that of $A'$. Note that the rule is allowed to depend on the chosen models and comparison maps, and takes the proofs as arguments.
--
--   `RepresentsOn r d E A ξ pt` is the conjunction of four conditions on such a rule. First, invariance: two data over the same $T$ related by isomorphisms $i_E, i_A$ of fake elliptic curves (in the sense of `IsoVia`: compatible with the group laws, $\Lambda$-equivariant, and matching the level subschemes) which commute with the comparison maps, $i_E g_{E''} = g_E$, $i_A g_{A''} = g_A$, and intertwine the isogenies, $\psi \circ i_E = i_A \circ \varphi$, receive the same point. Second, compatibility with base change: for an $S$-algebra map $f : T \to T'$ and data over $T'$ pulled back from data over $T$ along $f$, with the isogenies matching ($\psi$ followed by $h_A$ equals $h_E$ followed by $\varphi$, and symmetrically for $\psi', \varphi'$), the underlying morphism of the $T'$-point is $\operatorname{Spec} f$ followed by that of the $T$-point. Third, surjectivity: for every $S$-algebra $T$, every choice of models with comparison maps and every point of $X(T)$ over $\operatorname{Spec} S$, some level-preserving isogeny pair of degree $r^d$ is sent to it. Fourth, injectivity, stated for arbitrary test algebras $T$ and on the nose rather than up to isomorphism: if two level-preserving pairs $(\varphi_1,\varphi_1')$, $(\varphi_2,\varphi_2')$ for the same models give the same point, then $\varphi_1 = \varphi_2$ and $\varphi_1' = \varphi_2'$. No finiteness or finite-presentation requirement on $\xi$ is part of the predicate.
--
--   **Relation to Mathlib.** Mathlib has no notion of fake elliptic curve with quaternionic multiplication, nor of representability for such moduli problems; both the objects and this relation-style formulation of representability (predicates on chosen models and comparison morphisms, rather than functors and natural isomorphisms) are the project's own.
--
--   **Where it is used.** These predicates package the fixed-degree stratum of the moduli problem of isogeny pairs used in the Čerednik–Drinfeld description of Shimura curves: the rigidification data of a fake elliptic curve over a $p$-adic base are organised degree by degree in $r^d$, and each stratum is required to be represented by a scheme over the base in the sense defined here. This enters the construction of integral models of Shimura curves whose reduction feeds the level-lowering step of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMIsogenyPairRep.lean

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

abbrev PtFamily (r d : ℕ) {S : Type} [CommRing S] (E A : FakeEllipticCurve Λ N S)
    {X : Scheme.{0}} (ξ : X ⟶ Spec (CommRingCat.of S)) : Type 1 :=
  ∀ (T : Type) [CommRing T] [Algebra S T]
  (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
  (gA : A'.A ⟶ A.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
  (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f),
  FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ' → FakeEllipticCurve.PreservesLevel E' A' φ hφ →
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ξ

def RepresentsOn (r d : ℕ) {S : Type} [CommRing S] (E A : FakeEllipticCurve Λ N S)
    {X : Scheme.{0}} (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : PtFamily r d E A ξ) : Prop :=

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
          (E'' A'' : FakeEllipticCurve Λ N T) (gE'' : E''.A ⟶ E.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E'' gE'')
          (gA'' : A''.A ⟶ A.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' gA'')
          (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
          (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ') (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ)
          (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f) (iA : A'.A ≅ A''.A) (hiA : iA.hom ≫ A''.f = A'.f),
          FakeEllipticCurve.IsoVia E' E'' iE hiE → FakeEllipticCurve.IsoVia A' A'' iA hiA →
          iE.hom ≫ gE'' = gE → iA.hom ≫ gA'' = gA → iE.hom ≫ ψ = φ ≫ iA.hom →
            pt T E' A' gE hgE gA hgA φ φ' hφ hp hl = pt T E'' A'' gE'' hgE'' gA'' hgA'' ψ ψ' hψ hq hm) ∧

      (∀ (T T' : Type) [CommRing T] [Algebra S T] [CommRing T'] [Algebra S T'] (f : T →ₐ[S] T')
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
          (E'' A'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
          (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
          (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E'' (hE ≫ gE))
          (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') A A'' (hA ≫ gA))
          (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
          (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ') (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ),
          ψ ≫ hA = hE ≫ φ → ψ' ≫ hE = hA ≫ φ' →
            (pt T' E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ ψ' hψ hq hm).1 =
              Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫ (pt T E' A' gE hgE gA hgA φ φ' hφ hp hl).1) ∧

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ξ),
          ∃ (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
            (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
            pt T E' A' gE hgE gA hgA φ φ' hφ hp hl = z) ∧

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ₁ : E'.A ⟶ A'.A) (φ₁' : A'.A ⟶ E'.A) (hφ₁ : φ₁ ≫ A'.f = E'.f)
          (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₁ φ₁') (hl₁ : FakeEllipticCurve.PreservesLevel E' A' φ₁ hφ₁)
          (φ₂ : E'.A ⟶ A'.A) (φ₂' : A'.A ⟶ E'.A) (hφ₂ : φ₂ ≫ A'.f = E'.f)
          (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₂ φ₂') (hl₂ : FakeEllipticCurve.PreservesLevel E' A' φ₂ hφ₂),
          pt T E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ hl₁ = pt T E' A' gE hgE gA hgA φ₂ φ₂' hφ₂ hp₂ hl₂ → φ₁ = φ₂ ∧ φ₁' = φ₂')

end CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair


