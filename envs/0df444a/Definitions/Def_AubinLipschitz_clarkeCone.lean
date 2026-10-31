-- Prove2me | Definitions.Def_AubinLipschitz_clarkeCone
-- name    : AubinLipschitz_clarkeCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:06.279849+00:00
-- url     : https://prove2.me/theorems/85a36e06-b0a9-4de1-b2ef-d94ca0d38df5
-- title:
--   §1, Definition 3 — the Clarke tangent cone $C_K(x_0)$
-- statement:
--   Let $K$ be a subset of a normed space $X$ and $x_0\in X$. The **Clarke tangent cone** to $K$ at $x_0$ is the set $C_K(x_0)$ of all $v\in X$ such that for every $\varepsilon>0$ there are $\alpha>0$ and $\beta>0$ with the following property: for all $x\in K\cap(x_0+\alpha B)$ and all $h\in\,]0,\beta]$ there is $u\in v+\varepsilon B$ with
--
--   $$
--   x+hu\in K .
--   $$
--
--   Unlike the contingent cone, it asks for one direction to work uniformly from every point of $K$ near $x_0$ and for every small step. It is the graph of the Clarke derivative when $K$ is a graph.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §1, Definition 3, (10)–(11), p.9

import Mathlib

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §1, Definition 3, (10)–(11), p.9: the *Clarke tangent cone* `C_K(x₀)`. In the form
(11): `v ∈ C_K(x₀)` iff for every `ε > 0` there are `α > 0`, `β > 0` such that for all
`x ∈ B_K(x₀, α) = K ∩ (x₀ + αB)` and all `h ∈ ]0, β]` there is `u ∈ v + εB` with `x + h u ∈ K`.

**Formalization Note** Balls are closed, as in the paper (p.7); the quantification over `x` is
restricted to points of `K`. -/
def clarkeCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) (x₀ : E) :
    Set E :=
  {v | ∀ ε > 0, ∃ α > 0, ∃ β > 0, ∀ x ∈ K ∩ Metric.closedBall x₀ α, ∀ h : ℝ, 0 < h → h ≤ β →
    ∃ u ∈ Metric.closedBall v ε, x + h • u ∈ K}

end AubinLipschitz


