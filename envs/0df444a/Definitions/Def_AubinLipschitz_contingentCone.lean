-- Prove2me | Definitions.Def_AubinLipschitz_contingentCone
-- name    : AubinLipschitz_contingentCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:02.899+00:00
-- url     : https://prove2.me/theorems/5ebe3c10-2c03-4893-8d8b-04edd2e9d938
-- title:
--   §1, Definition 1 — the contingent cone $T_K(x)$
-- statement:
--   Let $K$ be a subset of a normed space $X$ and $x\in X$. The **contingent cone** to $K$ at $x$ is the set $T_K(x)$ of all $v\in X$ such that for every $\varepsilon>0$ and every $\alpha>0$ there are $u\in v+\varepsilon B$ and $h\in\,]0,\alpha]$ with
--
--   $$
--   x+hu\in K ,
--   $$
--
--   where $B$ is the closed unit ball. Equivalently, $v$ is a limit of difference quotients $(x_n-x)/h_n$ with $x_n\in K$ and $h_n\to0+$.
--
--   It is the first of the two tangent cones used throughout the mission; it is the graph of the contingent derivative when $K$ is the graph of a set-valued map.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §1, Definition 1, (1)–(2), p.7

import Mathlib

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §1, Definition 1, (1)–(2), p.7: the *contingent cone* `T_K(x)` to `K` at `x`. In the
form (2): `v ∈ T_K(x)` iff for all `ε > 0`, `α > 0` there are `u ∈ v + εB` and `h ∈ ]0, α]` with
`x + h u ∈ K`.

**Formalization Note** `εB` is the closed ball, as in the paper (p.7). `Mathlib`'s `tangentConeAt`
is not used, so that the definition reads as the source's. -/
def contingentCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) (x : E) :
    Set E :=
  {v | ∀ ε > 0, ∀ α > 0, ∃ u ∈ Metric.closedBall v ε, ∃ h : ℝ, 0 < h ∧ h ≤ α ∧ x + h • u ∈ K}

end AubinLipschitz


