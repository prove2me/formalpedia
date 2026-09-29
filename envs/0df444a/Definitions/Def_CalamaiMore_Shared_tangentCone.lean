-- Prove2me | Definitions.Def_CalamaiMore_Shared_tangentCone
-- name    : CalamaiMore_Shared_tangentCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:28:04.827443+00:00
-- url     : https://prove2.me/theorems/6ff7fa57-3e15-4993-8a20-209329e6d116
-- title:
--   Feasible directions and the tangent cone $T(x)$
-- statement:
--   Let $\Omega$ be a subset of a finite-dimensional real inner product space $E$ and let $x \in \Omega$. A direction $v \in E$ is **feasible** at $x$ if $x + \tau v \in \Omega$ for all $\tau > 0$ sufficiently small. The **tangent cone** of $\Omega$ at $x$ is the closure of the cone of feasible directions:
--
--   $$
--   T(x) = \overline{\{v \in E : \exists\, \bar\tau > 0,\ x + \tau v \in \Omega \text{ for all } \tau \in (0, \bar\tau)\}}.
--   $$
--
--   For a nonempty closed convex $\Omega$ and $x \in \Omega$, $T(x)$ is a nonempty closed convex cone; it is the set over which the projected gradient is defined.
--
--   This definition is shared by two missions of this series: I (convergence of the gradient projection method: the projected gradient (3.1), p. 101, and Lemma 3.1, p. 102) and II (active-set identification: the projected gradient (3.1), p. 101, Lemma 3.1, p. 102, and the polyhedral tangent cone, p. 105).
--
--   **Formalization Note** "For all $\tau > 0$ sufficiently small" is the filter statement `∀ᶠ τ in 𝓝[>] 0, x + τ • v ∈ Ω`; the set of such $v$ is already a cone, and `tangentCone Ω x` is its topological closure. It is defined in this general way, not by the polyhedral formula.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 101, §3 (definition of feasible direction and tangent cone)

import Mathlib

namespace CalamaiMore.Shared

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The feasible directions at `x` (Calamai–Moré, p. 101): the directions `v` such that
`x + τ v ∈ Ω` for all `τ > 0` sufficiently small. -/
def feasibleDirections (Ω : Set E) (x : E) : Set E :=
  {v | ∀ᶠ τ in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + τ • v ∈ Ω}

/-- The tangent cone `T(x)` (Calamai–Moré, p. 101): the closure of the cone of all feasible
directions at `x`. -/
def tangentCone (Ω : Set E) (x : E) : Set E :=
  closure (feasibleDirections Ω x)

end CalamaiMore.Shared


