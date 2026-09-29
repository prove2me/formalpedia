-- Prove2me | Definitions.Def_ChvatalPolytopes_SeriesParallel_IsSeriesParallel
-- name    : ChvatalPolytopes_SeriesParallel_IsSeriesParallel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:23:17.459979+00:00
-- url     : https://prove2.me/theorems/015b3d1c-8dc0-437b-acf6-40163c041bff
-- title:
--   Homeomorphs of $K_4$ and series-parallel networks (§7)
-- statement:
--   All graphs are finite, undirected and loopless. A **homeomorph of $K_4$** is a graph obtained from the complete graph $K_4$ when its edges are subdivided into paths by inserting new vertices of degree two.
--
--   A graph $G=(V,E)$ **contains a homeomorph of $K_4$** if it has a (not necessarily induced) subgraph which is a homeomorph of $K_4$. Equivalently, there are
--
--   1. four distinct *branch vertices* $b_0,b_1,b_2,b_3\in V$, and
--   2. for each of the six pairs $i<j$, a path $P_{ij}$ in $G$ from $b_i$ to $b_j$,
--
--   such that no path $P_{ij}$ passes through a branch vertex other than $b_i$ and $b_j$, and two different paths have no vertex in common other than branch vertices (so only a common endpoint). The complete graph $K_4$ itself, with every $P_{ij}$ a single edge, counts.
--
--   A **series-parallel network** is a graph which contains no homeomorph of $K_4$.
--
--   This is the class of graphs for which Theorem 7.1 asserts that the odd-cycle relaxation of the stable set problem and its dual have zero–one optima.
--
--   **Formalization Note** Mathlib has no notion of topological minor; containment is encoded directly by branch vertices `b : Fin 4 → V` (injective) and walks `p i j : G.Walk (b i) (b j)`, of which only those with `i < j` are constrained (each is a path, `Walk.IsPath`). The definition applies to any `SimpleGraph`, finite or not. It is neither "no $K_4$ minor" nor "built by series and parallel composition"; the equivalence with those notions is not part of the paper.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 150, §7 (homeomorph of K_4, series-parallel network)

import Mathlib

namespace ChvatalPolytopes.SeriesParallel

/-- `G` **contains a homeomorph of `K₄`** (Chvátal 1975, p. 150): `G` has a subgraph obtained
from `K₄` by subdividing its edges into paths by inserting new vertices of degree two.

Encoding: there are four distinct *branch vertices* `b 0, b 1, b 2, b 3` and, for each of the six
pairs `i < j`, a path `p i j` in `G` from `b i` to `b j` such that
* no path passes through a branch vertex other than its two endpoints, and
* two different paths share no vertex other than branch vertices (hence, by the previous
  condition, only common endpoints).
The walks `p i j` with `i ≥ j` are not used. `K₄` itself (every path a single edge) counts. -/
def ContainsK4Homeomorph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (b : Fin 4 → V) (p : ∀ i j : Fin 4, G.Walk (b i) (b j)),
    Function.Injective b ∧
    (∀ i j : Fin 4, i < j → (p i j).IsPath) ∧
    (∀ i j : Fin 4, i < j → ∀ k : Fin 4, b k ∈ (p i j).support → k = i ∨ k = j) ∧
    (∀ i j i' j' : Fin 4, i < j → i' < j' → (i, j) ≠ (i', j') →
      ∀ v : V, v ∈ (p i j).support → v ∈ (p i' j').support → ∃ k : Fin 4, v = b k)

/-- A **series-parallel network** (Chvátal 1975, p. 150): a graph which contains no homeomorph
of `K₄` (as a subgraph, not necessarily induced). -/
def IsSeriesParallel {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ ContainsK4Homeomorph G

end ChvatalPolytopes.SeriesParallel


