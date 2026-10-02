-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_IsLNaturalConvexPolyhedron
-- name    : DiscreteConvex_EconomicEquilibrium_IsLNaturalConvexPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:50:02.187116+00:00
-- url     : https://prove2.me/theorems/05639905-9bc0-46c9-bc4a-77deebbe950f
-- title:
--   L$^\natural$-convex polyhedron (SBS$^\natural$[R])
-- statement:
--   $P \subseteq \mathbb R^K$ is an **L$^\natural$-convex polyhedron** if it satisfies **(SBS$^\natural$[R])** (p.131): for all $p, q \in P$ and $\alpha \in \mathbb R_+$, $(p - \alpha\mathbf 1) \vee q \in P$ and $p \wedge (q + \alpha\mathbf 1) \in P$ (coordinatewise $\vee$, $\wedge$). This is the book's own working characterization of L$^\natural$-convexity for a (nonintegral) polyhedron (Eq. (5.20) identifies it with the restriction of an L-convex polyhedron to a coordinate plane). The case $\alpha = 0$ alone gives $p \vee q, p \wedge q \in P$, the "in particular" consequence Theorem 11.16 draws from L$^\natural$-convexity.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.131, axiom (SBS♮[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.131, axiom (SBS♮[R])

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.131, axiom (SBS♮[R]) (the working
characterization the book gives for "`P ⊆ Rᴷ` is L♮-convex", Eq. (5.20)): the L♮-convex
polyhedron property, in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- `P ⊆ Rᴷ` is an **L♮-convex polyhedron** if it satisfies (SBS♮[R]) (p.131): for all
`p, q ∈ P` and `α ∈ R₊`, `(p - α•1) ∨ q ∈ P` and `p ∧ (q + α•1) ∈ P` (coordinatewise `∨`, `∧`).
The case `α = 0` alone gives `p ∨ q, p ∧ q ∈ P`, the "in particular" consequence Theorem 11.16
draws from L♮-convexity. -/
def IsLNaturalConvexPolyhedron {K : Type*} (P : Set (K → ℝ)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∀ α : ℝ, 0 ≤ α →
    (fun k => max (p k - α) (q k)) ∈ P ∧ (fun k => min (p k) (q k + α)) ∈ P

end DiscreteConvex.EconomicEquilibrium


