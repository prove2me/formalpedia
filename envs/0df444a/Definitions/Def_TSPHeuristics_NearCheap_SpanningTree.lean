-- Prove2me | Definitions.Def_TSPHeuristics_NearCheap_SpanningTree
-- name    : TSPHeuristics_NearCheap_SpanningTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:55:26.485595+00:00
-- url     : https://prove2.me/theorems/c7e13739-3a71-41c0-af4d-3b233de2b1fb
-- title:
--   Length of a spanning tree
-- statement:
--   For a traveling salesman graph $(N, d)$ and a simple graph $M$ on the node set $N$, the **length** of $M$ is the sum of the lengths of its edges,
--
--   $$
--   w(M) = \sum_{\{i,j\} \in E(M)} d(i,j).
--   $$
--
--   When $M$ is a spanning tree of $N$ (connected and acyclic), $w(M)$ is the length of the tree, and **TREE**, the length of a minimal spanning tree for $(N,d)$, is the least $w(M)$ over all spanning trees $M$.
--
--   Spanning trees enter the analysis of nearest and cheapest insertion as the intermediate quantity between the heuristic's tour and the optimal tour.
--
--   **Formalization Note** An unordered edge $\{i,j\}$ is given the length $\tfrac12\bigl(d(i,j) + d(j,i)\bigr)$, which equals $d(i,j)$ for a symmetric distance and is well defined on unordered pairs. TREE itself is not introduced as a separate constant: statements about TREE are phrased over every spanning tree (upper bounds by TREE) or over some spanning tree (bounds on TREE), which is equivalent because TREE is attained.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 573, Lemma 3 (TREE, the length of a minimal spanning tree)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel

open Classical

namespace TSPHeuristics.NearCheap

/-- The length of an undirected edge `{i, j}`: `(d i j + d j i) / 2`, which is `d i j` for a
symmetric distance (symmetrized so that it is well defined on unordered pairs). -/
noncomputable def edgeLen {n : ℕ} (d : Fin n → Fin n → ℝ) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j => (d i j + d j i) / 2, fun i j => by ring⟩

/-- The length of a graph `M` on the nodes: the sum of the lengths of its edges. For a spanning
tree (`M.IsTree`) this is the length of the tree; TREE (p. 573) is its minimum over trees. -/
noncomputable def treeWeight {n : ℕ} (d : Fin n → Fin n → ℝ) (M : SimpleGraph (Fin n)) : ℝ :=
  ∑ e ∈ M.edgeFinset, edgeLen d e

end TSPHeuristics.NearCheap


