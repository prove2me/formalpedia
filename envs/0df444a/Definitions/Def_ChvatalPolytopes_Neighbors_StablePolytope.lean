-- Prove2me | Definitions.Def_ChvatalPolytopes_Neighbors_StablePolytope
-- name    : ChvatalPolytopes_Neighbors_StablePolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:20:07.600802+00:00
-- url     : https://prove2.me/theorems/395d099b-83d1-4b54-9279-94be10c44771
-- title:
--   Stable sets, $S(G)$ and the stable set polytope $P(G)$ (§2)
-- statement:
--   Let $G=(V,E)$ be a finite undirected loopless graph. A **stable set** of $G$ is a set of vertices no two of which are adjacent.
--
--   1. For a finite set $s\subseteq V$, its **incidence vector** $\chi^s\in\mathbb R^V$ has $\chi^s_u=1$ if $u\in s$ and $\chi^s_u=0$ otherwise.
--   2. $S(G)$ is the set of all zero–one vectors $(x_u:u\in V)$ such that $\{u : x_u=1\}$ is stable, i.e. the incidence vectors of the stable sets of $G$.
--   3. The **stable set polytope** is the convex hull
--   $$P(G)=\operatorname{conv} S(G)\subseteq\mathbb R^V.$$
--   4. For $y\in S(G)$, the **corresponding stable set** is $Y=\{u\in V : y_u=1\}$.
--
--   $S(G)$ is the vertex set of $P(G)$, and the question of the mission is which pairs of these vertices are joined by an edge of $P(G)$.
--
--   **Formalization Note** $V$ is a finite type with decidable equality and $G$ a `SimpleGraph V`. $S(G)$ is a set of functions `V → ℝ` (`stableVectors`), $P(G)$ is Mathlib's `convexHull ℝ (S G)`, and the corresponding stable set is `onesSet y = {u | y u = 1}`.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 139, §2 (stable set, S(G), P(G)); p. 149, Theorem 6.2 (corresponding stable sets)

import Mathlib

namespace ChvatalPolytopes.Neighbors

/-- The incidence vector `(x_u : u ∈ V)` of a finite vertex set `s`: `x_u = 1` if `u ∈ s`
and `x_u = 0` otherwise. -/
def incidenceVector {V : Type*} [DecidableEq V] (s : Finset V) : V → ℝ :=
  fun u => if u ∈ s then 1 else 0

/-- `S(G)` (Chvátal 1975, p. 139): the set of all zero–one vectors `(x_u : u ∈ V)` such that the
set `{u : x_u = 1}` is stable in `G`, i.e. the incidence vectors of the stable sets of `G`. -/
def stableVectors {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧ x = incidenceVector s}

/-- The stable set polytope `P(G)` (Chvátal 1975, pp. 138–139): the convex hull of `S(G)`
in `ℝ^V`. -/
def stablePolytope {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Set (V → ℝ) :=
  convexHull ℝ (stableVectors G)

/-- The stable set corresponding to a vector `y ∈ S(G)` (Chvátal 1975, p. 149, Theorem 6.2):
`Y = {u : y_u = 1}`. -/
def onesSet {V : Type*} (y : V → ℝ) : Set V :=
  {u | y u = 1}

end ChvatalPolytopes.Neighbors


