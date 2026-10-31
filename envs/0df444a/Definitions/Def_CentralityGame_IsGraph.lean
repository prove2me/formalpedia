-- Prove2me | Definitions.Def_CentralityGame_IsGraph
-- name    : CentralityGame_IsGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:11:42.342192+00:00
-- url     : https://prove2.me/theorems/154204f8-b4dd-4103-b761-58ec2d3e5174
-- title:
--   Graph: no self-loops and no sink nodes
-- statement:
--   A **graph** is a finite directed graph $\mathcal G=(\mathcal V,\mathcal E)$ with node set $\mathcal V$ and link set $\mathcal E\subseteq\mathcal V\times\mathcal V$ that contains no self-loops and has no sink nodes. Writing $\mathcal N_i=\{j:(i,j)\in\mathcal E\}$ for the out-neighbourhood of $i$ and $d_i=|\mathcal N_i|$ for its out-degree, this means
--
--   $$
--   i\notin\mathcal N_i\quad\text{and}\quad d_i\ge 1\qquad\text{for every } i\in\mathcal V.
--   $$
--
--   This is the standing notion of graph on which walks, reachability, the normalized adjacency matrix and PageRank are defined.
--
--   **Formalization Note** The link set is given by the map $i\mapsto\mathcal N_i$ into finite sets of nodes.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §2, pp.4–5

import Mathlib

namespace CentralityGame

/-- A **graph** in the sense of Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §2, pp.4–5: a finite directed graph
`G = (V, E)` with no self-loops and no sink nodes (`d_i ≥ 1` for every `i`), presented by its
out-neighbourhoods `N_i = {j : (i, j) ∈ E}`.

**Formalization Note** The link set is encoded by `N : V → Finset V`, with `(i, j) ∈ E` iff
`j ∈ N i`, and the out-degree `d_i = |N_i|` is `(N i).card`. Every `N` with these two
properties is a graph of the paper and conversely. -/
def IsGraph {V : Type*} (N : V → Finset V) : Prop :=
  (∀ i, i ∉ N i) ∧ ∀ i, (N i).Nonempty

end CentralityGame


