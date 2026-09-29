-- Prove2me | Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope
-- name    : ChvatalPolytopes_Perfect_StablePolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:11:55.557472+00:00
-- url     : https://prove2.me/theorems/b0a1b63f-e6c6-4475-87c9-22723eb30a2e
-- title:
--   Stable sets, the stable set polytope $P(G)$ and the maximal cliques $C(G)$ (§2)
-- statement:
--   Let $G=(V,E)$ be a finite undirected loopless graph. A **stable set** of $G$ is a set of vertices no two of which are adjacent; a **clique** of $G$ is a *maximal* complete subgraph.
--
--   1. For a finite set $s\subseteq V$, its **incidence vector** $\chi^s\in\mathbb R^V$ has $\chi^s_u=1$ if $u\in s$ and $\chi^s_u=0$ otherwise.
--   2. $S(G)$ is the set of all zero–one vectors $(x_u:u\in V)$ such that $\{u : x_u=1\}$ is stable, i.e. the incidence vectors of the stable sets of $G$.
--   3. The **stable set polytope** is the convex hull
--   $$P(G)=\operatorname{conv} S(G)\subseteq\mathbb R^V.$$
--   4. $C(G)$ is the set of vertex sets $W\subseteq V$ of the cliques of $G$: the sets $W$ that are complete in $G$ and are not properly contained in any larger complete set.
--
--   These are the objects about which every statement of the mission is made: $P(G)$ is the polytope whose linear description is sought, and the clique inequalities $\sum_{u\in W}x_u\le 1$, $W\in C(G)$, are the candidate description.
--
--   **Formalization Note** $V$ is a finite type with decidable equality and $G$ a `SimpleGraph V`. $S(G)$ is a set of functions `V → ℝ`, and $P(G)$ is Mathlib's `convexHull ℝ (S G)`. $C(G)$ is the `Finset (Finset V)` of finsets that are `Maximal` for the property "is a clique of $G$"; on the empty vertex type the only maximal clique is $\emptyset$. A structural lemma `mem_maximalCliques` unfolds membership.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), pp. 138–139, §1 and §2 (definitions of stable set, clique, S(G), P(G), C(G))

import Mathlib

namespace ChvatalPolytopes.Perfect

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

/-- `C(G)` (Chvátal 1975, p. 139): the vertex sets `W` of the cliques of `G`, where a *clique* is
a **maximal** complete subgraph; i.e. the finsets `W` that are complete in `G` and are not
properly contained in any complete finset. -/
noncomputable def maximalCliques {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun W : Finset V => Maximal (fun W : Finset V => G.IsClique (W : Set V)) W)

theorem mem_maximalCliques {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) :
    W ∈ maximalCliques G ↔ Maximal (fun W : Finset V => G.IsClique (W : Set V)) W := by
  unfold maximalCliques
  simp

end ChvatalPolytopes.Perfect


