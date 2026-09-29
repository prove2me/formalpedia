-- Prove2me | Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
-- name    : CerednikDrinfeld_QMFormalCompletionAlong
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/ab4f00c3-e24f-5df2-a778-7138fefd1276
-- title:
--   Formal completion of a morphism along unit sections
-- statement:
--   Fix a commutative ring $B$ and two $B$-schemes $f : A \to \operatorname{Spec} B$ and $f' : A' \to \operatorname{Spec} B$. Recall that a family of formal coordinates `RelativeGroupLaw.FormalCoordinates f g` is simply an assignment, to every $B$-algebra $B'$ and every $g$-tuple $s \in (B')^g$, of a $B'$-point of $A$ over $\operatorname{Spec} B$, i.e. an element of $\mathrm{Hom}_{\operatorname{Spec} B}(\operatorname{Spec} B', A)$; no axiom is part of that type. Given such data $\theta$ in $g$ variables for $f$ and $\theta'$ in $g'$ variables for $f'$, a morphism $h : A \to A'$ with $h$ followed by $f'$ equal to $f$, and a $g'$-tuple $\varphi = (\varphi_i)_{i < g'}$ of formal power series in $g$ variables over $B$, the predicate `IsFormalCompletionAlong` asserts: for every $B$-algebra $B'$, every ideal $J \subseteq B'$, every $n$ with $J^{n+1} = 0$, and every $s : \mathrm{Fin}\,g \to B'$ with all $s_i \in J$,
--   $$\theta'\bigl(B'; (\,\mathrm{nilEval}\,n\,\varphi_i\,s\,)_i\bigr) = \mathrm{mapPt}\,h\,(\theta(B'; s)).$$
--   Here [`MvFormalGroup.nilEval n (φ i) s`](../def/AlgebraicGeometry_FormalGroupAlongSection.html#L15) is the value at $s$ of the truncation of $\varphi_i$ to multidegrees with every exponent at most $n$ (a well-defined substitute for $\varphi_i(s)$, since monomials of total degree $> n$ vanish on $J$), and `mapPt h hh` is the operation of composing a point of $A$ with $h$ to obtain a point of $A'$ over the same base.
--
--   Thus the predicate says that, on all points with coordinates in a nilpotent ideal, $h$ is given in the coordinates $\theta, \theta'$ by the tuple of power series $\varphi$; it is a relation between a chosen presentation $\theta$, $\theta'$ and $\varphi$, constraining $\theta$ and $\theta'$ only on such tuples, and imposing no condition of its own on $\varphi$ (such as vanishing constant term) nor requiring $\theta$, $\theta'$ to be formal coordinates for group laws.
--
--   **Relation to Mathlib.** Multivariate power series and their truncations are Mathlib's (`MvPowerSeries`, `MvPowerSeries.trunc'`); the functor-of-points formalism used here for relative group laws, formal coordinates along a unit section and the induced power-series expansion of a morphism is the project's own, with no Mathlib counterpart.
--
--   **Where it is used.** This relation is used in the Čerednik–Drinfeld part of the development, where formal coordinates along the unit sections of fake elliptic curves are compared: it expresses that a tuple of power series is the formal expansion of a given morphism of abelian schemes (for instance a rigidification of a quasi-isogeny from a fixed supersingular object), which is how endomorphisms and quasi-isogenies are transported to the formal modules attached to the quaternionic moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMFormalCompletionAlong.lean

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace CerednikDrinfeld.QM

def IsFormalCompletionAlong {B : Type} [CommRing B] {A A' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {g g' : ℕ}
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    (h : A ⟶ A') (hh : h ≫ f' = f) (φ : Fin g' → MvPowerSeries (Fin g) B) : Prop :=
  ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ), J ^ (n + 1) = ⊥ →
    ∀ s : Fin g → B', (∀ i, s i ∈ J) →
      θ' B' (fun i => MvFormalGroup.nilEval n (φ i) s) = mapPt h hh (θ B' s)

end CerednikDrinfeld.QM

end


