-- Prove2me | Definitions.Def_CerednikDrinfeld_QMIsogeny
-- name    : CerednikDrinfeld_QMIsogeny
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/30122863-6c6a-586c-9447-daa1cea43e53
-- title:
--   Isogenies of fake elliptic curves and level preservation
-- statement:
--   Throughout, $a,b$ are rationals, $\Lambda$ a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, $N$ a natural number and $S$ a commutative ring; a `FakeEllipticCurve Λ N S` is the project's moduli datum consisting of a scheme $E.A$ over $\operatorname{Spec} S$ carrying a commutative relative group law on its functor of points, the abelian-scheme property bundle, two-dimensional fibres, an action `act` of $\Lambda$ by endomorphisms over $S$ subject to additivity, multiplicativity and a trace condition, together with a closed subscheme `lev` playing the role of a level-$N$ structure.
--
--   `IsIsogenyPair d E E' φ ψ` asserts, for $\varphi : E.A \to E'.A$ and $\psi : E'.A \to E.A$, the existence of witnesses that both are morphisms over $\operatorname{Spec} S$ ($\varphi$ followed by $E'.f$ equals $E.f$, and symmetrically for $\psi$) such that: composition with $\varphi$, resp. $\psi$, is additive on $T$-valued points for every scheme $T$ over $\operatorname{Spec} S$; both commute with the $\Lambda$-actions, in the form $E.\mathrm{act}(x)$ followed by $\varphi$ equals $\varphi$ followed by $E'.\mathrm{act}(x)$ for all $x \in \Lambda$, and dually for $\psi$; and, for every proof that the image of $d$ in $\mathbb{H}[\mathbb{Q},a,b]$ lies in $\Lambda$, that $\varphi$ followed by $\psi$ is $E.\mathrm{act}(d)$ and $\psi$ followed by $\varphi$ is $E'.\mathrm{act}(d)$. The last clause is conditional, hence vacuous when $d \notin \Lambda$; no condition is imposed on kernels, and no compatibility with the level structures is required. `IsIsogeny d E E'` existentially quantifies over such a pair $(\varphi,\psi)$. Separately, `PreservesLevel E E' φ hφ` says that $\varphi$ carries level points to level points: whenever a $T$-point of $E$ factors through $E.\mathrm{lev}$, its image under composition with $\varphi$ factors through $E'.\mathrm{lev}$. With these notions, the predicate `HeckeNeighbour ℓ` of the moduli module is the conjunction of `IsIsogenyPair ℓ`, level preservation in both directions, and the requirement that neither map be an isomorphism.
--
--   **Relation to Mathlib.** Mathlib has no notion of abelian scheme, of quaternionic multiplication, or of isogeny of abelian schemes; these predicates are the project's own, formulated through the functor-of-points group law `RelativeGroupLaw` rather than through a group-scheme structure.
--
--   **Where it is used.** These predicates express the Hecke correspondence and the isogeny relations on the moduli description of Shimura curves attached to an indefinite rational quaternion algebra, as used in the Čerednik–Drinfeld analysis of the reduction of such curves and in the Jacobian-torsion data feeding Ribet's level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMIsogeny.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

def IsIsogenyPair (d : ℕ) (E E' : FakeEllipticCurve Λ N S) (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A) : Prop :=
  ∃ (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E.f = E'.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧ (∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x) ∧
    (∀ hd : ((d : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ ∧ ψ ≫ φ = E'.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩)

def IsIsogeny (d : ℕ) (E E' : FakeEllipticCurve Λ N S) : Prop :=
  ∃ (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A), IsIsogenyPair d E E' φ ψ

def PreservesLevel (E E' : FakeEllipticCurve Λ N S) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough E.lev P → FactorsThrough E'.lev (mapPt φ hφ P)

end CerednikDrinfeld.QM.FakeEllipticCurve

end


