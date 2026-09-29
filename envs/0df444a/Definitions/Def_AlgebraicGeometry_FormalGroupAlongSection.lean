-- Prove2me | Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
-- name    : AlgebraicGeometry_FormalGroupAlongSection
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/8c45f872-bb5e-5d1d-9f03-614ba21d66ee
-- title:
--   Formal group laws along the unit section of a relative group law
-- statement:
--   Throughout, $B$ is a commutative ring and $f : A \to \operatorname{Spec} B$ a scheme over $\operatorname{Spec} B$ carrying a relative group law $L$, i.e. a functorial group structure on the sets $\mathrm{SchemeHomOver}\,(t, f)$ of $A$-valued points over $\operatorname{Spec} B$, with multiplication, unit and inverse, the group axioms and naturality along base changes $\psi$ as fields. Two auxiliary operations handle substitution of nilpotent arguments into power series. For a finite index type $\sigma$, a $B$-algebra $B'$, a natural number $n$, a series $\varphi \in B[[X_\sigma]]$ and a tuple $a : \sigma \to B'$, [`MvFormalGroup.nilEval`](../def/AlgebraicGeometry_FormalGroupAlongSection.html#L15) truncates $\varphi$ by the exponent bound $n$ in each variable and evaluates the resulting polynomial at $a$ through the structure map $B \to B'$. For $F$ a $g$-dimensional formal group law over $B$ (a $g$-tuple of series in $2g$ variables with vanishing constant term, linear part $X_i^{(1)} + X_i^{(2)}$, and the associativity identity as a field of the structure), [`MvFormalGroup.nilMul`](../def/AlgebraicGeometry_FormalGroupAlongSection.html#L19) applies this truncated evaluation componentwise to the concatenated tuple $\mathrm{Sum.elim}\,s\,t$, giving $F(s,t)$ for tuples $s,t$ over $B'$.
--
--   Given an ideal $J \subseteq B'$, a point $P : \operatorname{Spec} B' \to A$ over $\operatorname{Spec} B$ satisfies `IsInfinitesimal J P` when its restriction along $\operatorname{Spec}(B'/J) \to \operatorname{Spec} B'$ equals the unit $L.\mathrm{one}$ at $\operatorname{Spec}(B'/J)$, i.e. $P$ reduces modulo $J$ to the unit section. [`FormalCoordinates f g`](../def/WeierstrassCurve_ZeroComponentReduction.html#L28) is the type of families $\theta$ assigning to each $B$-algebra $B'$ and each tuple in $(B')^g$ a point of $A$ over $\operatorname{Spec} B$. The predicate `IsFormalCoordinates L F θ` asks: (i) naturality, $\theta_{B''}(\varphi \circ s) = \operatorname{Spec}(\varphi)^* \theta_{B'}(s)$ for every $B$-algebra map $\varphi : B' \to B''$ and every tuple $s$ with all entries nilpotent; and (ii) for every $B$-algebra $B'$, ideal $J$ and $n$ with $J^{n+1} = \bot$: tuples with entries in $J$ give infinitesimal points, $\theta_{B'}$ is injective on such tuples, every $J$-infinitesimal point is $\theta_{B'}(s)$ for such a tuple, and $\theta_{B'}(F.\mathrm{nilMul}\,n\,s\,t) = L.\mathrm{mul}(\theta_{B'}(s), \theta_{B'}(t))$. Thus $\theta_{B'}$ is a bijection $J^g \to \{P : P \equiv e \bmod J\}$ transporting the truncated law $F$ to the group law of $L$; the values of $\theta$ on non-nilpotent tuples are unconstrained. Finally `IsFormalGroupAlong L F` asserts the existence of such a $\theta$; it is a property of the pair $(L, F)$, a compatibility with a chosen presentation of the formal group rather than an isomorphism of formal schemes.
--
--   **Relation to Mathlib.** The truncation and substitution calculus for `MvPowerSeries` is Mathlib's; the multivariate formal group law structure, the functor-of-points relative group law, and the predicates relating the two along the unit section are the project's own.
--
--   **Where it is used.** These definitions let an explicitly presented formal group law be docked to the group law on the points of a group scheme over a base, so that infinitesimal neighbourhoods of the identity can be computed with power series. They are used in the treatment of good reduction of Jacobians and in the Čerednik–Drinfeld material, where the formal module attached to a fake elliptic curve and deformation arguments on nilpotent thickenings are formulated in these terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_FormalGroupAlongSection.lean

import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace MvFormalGroup

variable {B : Type} [CommRing B]

def nilEval {σ : Type} [Fintype σ] [DecidableEq σ] {B' : Type} [CommRing B'] [Algebra B B']
    (n : ℕ) (φ : MvPowerSeries σ B) (a : σ → B') : B' :=
  MvPolynomial.aeval a (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => n) φ)

def nilMul {g : ℕ} (F : MvFormalGroup g B) {B' : Type} [CommRing B'] [Algebra B B'] (n : ℕ)
    (s t : Fin g → B') : Fin g → B' :=
  fun i => nilEval n (F.toPowerSeries i) (Sum.elim s t)

end MvFormalGroup

namespace GoodReductionJacobian.RelativeGroupLaw

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}

def IsInfinitesimal (L : RelativeGroupLaw B f) {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B')
    (P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f) : Prop :=
  schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
      (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)) P =
    L.one (Scheme.specOver (𝒪 := B) (B' ⧸ J))

abbrev FormalCoordinates (f : A ⟶ Spec (CommRingCat.of B)) (g : ℕ) : Type 1 :=
  ∀ (B' : Type) [CommRing B'] [Algebra B B'], (Fin g → B') → SchemeHomOver (Scheme.specOver (𝒪 := B) B') f

def IsFormalCoordinates (L : RelativeGroupLaw B f) {g : ℕ} (F : MvFormalGroup g B) (θ : FormalCoordinates f g) : Prop :=

    (∀ (B' : Type) [CommRing B'] [Algebra B B'] (B'' : Type) [CommRing B''] [Algebra B B''] (φ : B' →ₐ[B] B'')
        (s : Fin g → B'), (∀ i, IsNilpotent (s i)) →
        θ B'' (φ ∘ s) = schemeHomOverComp (Spec.map (CommRingCat.ofHom φ.toRingHom))
          (Scheme.specMap_algHom_comp_specOver φ) (θ B' s)) ∧

    (∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ), J ^ (n + 1) = ⊥ →
        (∀ s : Fin g → B', (∀ i, s i ∈ J) → L.IsInfinitesimal J (θ B' s)) ∧
        (∀ s t : Fin g → B', (∀ i, s i ∈ J) → (∀ i, t i ∈ J) → θ B' s = θ B' t → s = t) ∧
        (∀ P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f, L.IsInfinitesimal J P →
          ∃ s : Fin g → B', (∀ i, s i ∈ J) ∧ θ B' s = P) ∧
        (∀ s t : Fin g → B', (∀ i, s i ∈ J) → (∀ i, t i ∈ J) →
          θ B' (F.nilMul n s t) = L.mul (Scheme.specOver (𝒪 := B) B') (θ B' s) (θ B' t)))

def IsFormalGroupAlong (L : RelativeGroupLaw B f) {g : ℕ} (F : MvFormalGroup g B) : Prop :=
  ∃ θ : FormalCoordinates f g, L.IsFormalCoordinates F θ

end GoodReductionJacobian.RelativeGroupLaw


