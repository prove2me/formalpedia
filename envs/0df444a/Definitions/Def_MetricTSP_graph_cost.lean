-- Prove2me | Definitions.Def_MetricTSP_graph_cost
-- name    : MetricTSP_graph_cost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-24T19:54:21.499313+00:00
-- url     : https://prove2.me/theorems/12c5b54c-1774-4db4-8fac-9b1e674cf0a7
-- title:
--   Edge cost of a graph on the cities
-- statement:
--   The total edge cost of a graph on the $n$ cities, the quantity compared against the Held--Karp relaxation in the classical tree-based analyses of metric TSP.
--
--   1. `pairCost` $c\,e$ is the cost of an unordered pair $e = \{u,v\}$: the symmetrization $\tfrac12(c(u,v) + c(v,u))$, which for a symmetric cost function (the only case of interest) is just $c(u,v)$. Symmetrizing makes the definition well-defined on unordered pairs without carrying a symmetry hypothesis.
--   2. `graphCost` $c\,G$ is the sum of `pairCost` over the edge set of a simple graph $G$ on the cities: $\sum_{e \in E(G)} c(e)$.
--
--   For a spanning tree $T$, $\mathrm{graphCost}(c, T)$ is the tree cost appearing in the tree-doubling bound $\mathrm{OPT} \le 2\,\mathrm{MST}$ and in Christofides' algorithm; the fractional counterpart is the bound $\mathrm{MST} \le \mathrm{LP}$ of Held--Karp analyses.
--
--   **Formalization Note.** The edge set is materialized as a `Finset` with a classical choice of `Fintype` instance; `graphCost` is `noncomputable` for this reason.
-- source:
--   M. Held, R. M. Karp, The traveling-salesman problem and minimum spanning trees, Operations Research 18 (1970) 1138-1162 (spanning trees against the Held--Karp bound); D. P. Williamson, D. B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press 2011, Sections 2.4 and 11.2 (the double-tree algorithm and the subtour LP).

import Mathlib

namespace MetricTSP

/-- The cost of an unordered pair of cities under a cost function `c`: the value of
`c` symmetrized over the two orientations, so that the definition does not depend on
a symmetry hypothesis. For a symmetric `c` (the only case of interest) this is just
`c u v` on the pair `{u, v}`. -/
noncomputable def pairCost {n : ℕ} (c : Fin n → Fin n → ℝ) (e : Sym2 (Fin n)) : ℝ :=
  Sym2.lift ⟨fun u v => (c u v + c v u) / 2, fun u v => by ring⟩ e

open Classical in
/-- The cost of (the edge set of) a graph on the `n` cities: the sum of the pair
costs of its edges. For a spanning tree this is the tree cost compared against the
Held–Karp relaxation in the tree-doubling and Christofides analyses. -/
noncomputable def graphCost {n : ℕ} (c : Fin n → Fin n → ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ e ∈ G.edgeSet.toFinset, pairCost c e

end MetricTSP


