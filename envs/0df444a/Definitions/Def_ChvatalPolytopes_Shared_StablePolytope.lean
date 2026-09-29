-- Prove2me | Definitions.Def_ChvatalPolytopes_Shared_StablePolytope
-- name    : ChvatalPolytopes_Shared_StablePolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:16:23.088199+00:00
-- url     : https://prove2.me/theorems/9411c1cb-4084-4db8-b7d6-a3c7c59027fe
-- title:
--   Stable sets and the stable set polytope $P(G)$ (§§1–2)
-- statement:
--   Let $G=(V,E)$ be a finite undirected loopless graph. A **stable set** of $G$ is a set of vertices no two of which are adjacent.
--
--   1. For a finite set $s\subseteq V$, its **incidence vector** $\chi^s\in\mathbb R^V$ has $\chi^s_u=1$ if $u\in s$ and $\chi^s_u=0$ otherwise.
--   2. $S(G)$ is the set of all zero–one vectors $(x_u:u\in V)$ such that $\{u : x_u=1\}$ is stable, i.e. the incidence vectors of the stable sets of $G$.
--   3. The **stable set polytope** of $G$ is the convex hull
--   $$P(G)=\operatorname{conv} S(G)\subseteq\mathbb R^V.$$
--
--   Used by two missions of this paper: 02-clique-separations (Theorems 4.1 and 4.2, which say which linear inequalities describe $P(G)$ and which of them are facets; definitions of §§1–2, pp. 138–139) and 03-substitution (Theorem 5.1, which builds a defining linear system of $P(G)$ for a substituted graph; definitions of §§1–2, pp. 138–139).
--
--   **Formalization Note** $V$ is a finite type with decidable equality and $G$ a `SimpleGraph V`. $S(G)$ is a set of functions `V → ℝ` and $P(G)$ is Mathlib's `convexHull ℝ (S G)`. For an induced subgraph $G_A$ (`G.induce A`) the same definitions apply on the subtype of $A$. A defining linear system is not a separate definition: each theorem states the set equality between the solution set and $P(G)$ directly.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), pp. 138–139, §1 and §2 (definitions of stable set, S(G), P(G))

import Mathlib

namespace ChvatalPolytopes.Shared

/-- The incidence vector `(x_u : u ∈ V)` of a finite vertex set `s`: `x_u = 1` if `u ∈ s`
and `x_u = 0` otherwise. -/
def incidenceVector {V : Type*} [DecidableEq V] (s : Finset V) : V → ℝ :=
  fun u => if u ∈ s then 1 else 0

/-- `S(G)` (Chvátal 1975, p. 139): the set of all zero–one vectors `(x_u : u ∈ V)` such that the
set `{u : x_u = 1}` is stable in `G`, i.e. the incidence vectors of the stable sets of `G`. -/
def stableVectors {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧ x = incidenceVector s}

/-- The stable set polytope `P(G)` (Chvátal 1975, pp. 138–139): the convex hull of `S(G)`
in `ℝ^V`, i.e. the convex hull of the incidence vectors of all stable sets of `G`. -/
def stablePolytope {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Set (V → ℝ) :=
  convexHull ℝ (stableVectors G)

end ChvatalPolytopes.Shared


