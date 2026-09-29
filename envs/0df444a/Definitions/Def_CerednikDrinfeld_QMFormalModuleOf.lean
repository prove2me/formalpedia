-- Prove2me | Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
-- name    : CerednikDrinfeld_QMFormalModuleOf
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/5f16fdcb-6c47-5c3c-80d0-1c544e591ef3
-- title:
--   Order coordinates and formal OD​-modules of fake elliptic curves
-- statement:
--   Throughout, $q$ is a prime and $\mathrm{Zp2}\,q = \mathrm{WittVector}\,q\,(\mathrm{GaloisField}\,q\,2)$ denotes the Witt vectors of $\mathbb{F}_{q^2}$, i.e. the ring of integers of the unramified quadratic extension of $\mathbb{Q}_q$, with $\sigma =$ `WittVector.frobenius`.
--
--   The structure `IsOrderCoord Λ q coord` is a predicate on a chosen map $\mathrm{coord}\colon\Lambda\to \mathrm{Zp2}\,q\times\mathrm{Zp2}\,q$, written $m\mapsto(\alpha_m,\beta_m)$, where $\Lambda$ is a $\mathbb{Z}$-submodule of the rational quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$. Its fields require: additivity; $\mathrm{coord}(1)=(1,0)$ whenever $1\in\Lambda$; multiplicativity for the twisted law $(\alpha,\beta)(\alpha',\beta')=(\alpha\alpha'+q\,\beta\,\sigma\beta',\ \alpha\beta'+\beta\,\sigma\alpha')$, imposed for those $m,m'$ whose product again lies in $\Lambda$; injectivity; $q$-adic density, namely for every $k$ and every $(\alpha,\beta)$ some $m\in\Lambda$ with both components of $\mathrm{coord}(m)-(\alpha,\beta)$ in the ideal $(q^k)$; and the trace condition: if $m+\bar m$ equals the rational integer $n$, then $\alpha_m+\sigma\alpha_m=n$. Thus $\Lambda$ is coordinatised inside the maximal order $\mathbb{Z}_{q^2}\oplus\mathbb{Z}_{q^2}\Pi$ of the quaternion division algebra over $\mathbb{Q}_q$, rather than an abstract isomorphism being asserted.
--
--   For a fake elliptic curve $E$ over $B$ (a relative group law with $\Lambda$-action and level subscheme) the predicate `IsFormalModuleVia E coord X θ` says that $\theta$, a system of two-dimensional formal coordinates for $E.f$, is a system of formal coordinates for the group law `E.L` with associated formal group law $X.F$ (compatibility with base change on nilpotent arguments, and for each ideal $J$ with $J^{n+1}=0$: infinitesimality, injectivity and surjectivity onto infinitesimal points, and transport of the truncated group law), and that for every $B$-algebra $B'$, every $J$ with $J^{n+1}=\bot$, every $m\in\Lambda$ and every $s$ with entries in $J$, the truncated evaluation at $s$ of the series $X.\mathrm{act}(\alpha_m)+_{X.F}\bigl(X.\mathrm{act}(\beta_m)\circ X.\varpi\bigr)$ is carried by $\theta$ to the push-forward of $\theta(s)$ along the endomorphism $E.\mathrm{act}\,m$. Here $X$ is a `FormalODModule q B`: a commutative two-dimensional formal group law with a ring action of $\mathrm{Zp2}\,q$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=\mathrm{act}(q)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$. `IsFormalModuleOf E coord X` existentially quantifies $\theta$.
--
--   The auxiliary `IsPullbackVia φ E E' g` is the base-change relation between fake elliptic curves over $S$ and over $S'$ along $\varphi\colon S\to S'$ with the comparison morphism $g\colon E'.A\to E.A$ named: the square formed by $g$, $E'.f$, $E.f$ and $\mathrm{Spec}\,\varphi$ is a pullback, $g$ transports the group law (stated on underlying morphisms of points), it intertwines the two $\Lambda$-actions, and every point factoring through $E'.\mathrm{lev}$ becomes, after composition with $g$, a point factoring through $E.\mathrm{lev}$ — this last clause an implication only, not an equivalence.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient ingredients — `WittVector` and its Frobenius, `GaloisField`, `MvPowerSeries`, schemes and `CategoryTheory.IsPullback` — while formal group laws in several variables, formal $\mathcal{O}_D$-modules, fake elliptic curves with $\Lambda$-action and level subscheme, and formal coordinates along the unit section of a relative group law are the project's own notions.
--
--   **Where it is used.** These definitions set up the local comparison underlying the Čerednik–Drinfeld description of a Shimura curve at a prime $q$ of ramification of the quaternion algebra: a fake elliptic curve over a $q$-nilpotent base is attached to the formal $\mathcal{O}_D$-module obtained from its formal group in suitable coordinates, with the $\Lambda$-action read off through `coord`. The resulting moduli description of the reduction at $q$ feeds the level-lowering part of the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped Quaternion

namespace CerednikDrinfeld.QM

structure IsOrderCoord {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (q : ℕ) [Fact q.Prime] (coord : ↥Λ → Zp2 q × Zp2 q) : Prop where
  map_add : ∀ m m' : ↥Λ, coord (m + m') = coord m + coord m'
  map_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, coord ⟨1, h⟩ = (1, 0)
  map_mul : ∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
    coord ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ =
      ((coord m).1 * (coord m').1 + (q : Zp2 q) * ((coord m).2 * WittVector.frobenius (coord m').2),
        (coord m).1 * (coord m').2 + (coord m).2 * WittVector.frobenius (coord m').1)
  injective : Function.Injective coord
  dense : ∀ (k : ℕ) (α β : Zp2 q), ∃ m : ↥Λ,
    (coord m).1 - α ∈ Ideal.span {((q : Zp2 q)) ^ k} ∧ (coord m).2 - β ∈ Ideal.span {((q : Zp2 q)) ^ k}
  trace : ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
    (coord m).1 + WittVector.frobenius (coord m).1 = (n : Zp2 q)

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime] {B : Type} [CommRing B]

def IsPullbackVia {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (g : E'.A ⟶ E.A) : Prop :=
  ∃ (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
      (E'.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
    (∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x) ∧
    (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
      FactorsThrough E'.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g)

def IsFormalModuleVia (E : FakeEllipticCurve Λ N B) (coord : ↥Λ → Zp2 q × Zp2 q) (X : FormalODModule q B)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) : Prop :=
  E.L.IsFormalCoordinates X.F θ ∧
    ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ (m : ↥Λ) (s : Fin 2 → B'), (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval n
            (Series.addVia X.F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi) i) s) =
          pushPt (E.act m) (E.act_over m) (θ B' s)

def IsFormalModuleOf (E : FakeEllipticCurve Λ N B) (coord : ↥Λ → Zp2 q × Zp2 q) (X : FormalODModule q B) : Prop :=
  ∃ θ : RelativeGroupLaw.FormalCoordinates E.f 2, E.IsFormalModuleVia coord X θ

end FakeEllipticCurve

end CerednikDrinfeld.QM


