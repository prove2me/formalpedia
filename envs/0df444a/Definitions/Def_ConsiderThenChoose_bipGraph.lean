-- Prove2me | Definitions.Def_ConsiderThenChoose_bipGraph
-- name    : ConsiderThenChoose_bipGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:30:31.601554+00:00
-- url     : https://prove2.me/theorems/4f31d2bf-ad4b-405c-909f-23e7a5defe77
-- title:
--   The product–type bipartite graph $G = ([N],[K],E)$
-- statement:
--   Consider an assortment instance with $N$ products and $K$ customer types. Each customer type $j$ has a **consideration set** $C_j \subseteq [N]$, the products it is willing to buy. Under a unique ranking the products are numbered in preference order, product $1$ being the most preferred.
--
--   The **graph representation** of the instance is the bipartite graph $G = ([N],[K],E)$ whose two sides are the products and the customer types, with an edge between product $i$ and type $j$ exactly when type $j$ considers product $i$:
--
--   $$
--   E = \{(i,j) \in [N] \times [K] : i \in C_j\}.
--   $$
--
--   There are no edges between two products or between two types. The connected components of this graph and of its induced subgraphs drive the dynamic program of Aouad, Farias and Levi.
--
--   **Formalization Note** Products are `Fin N` and types `Fin K`, both 0-based; product `0` is the paper's product $1$ (the most preferred). The vertex type is `Fin N ⊕ Fin K`, products on the left and types on the right, and the graph is `SimpleGraph.fromRel` of the relation "product $i$, type $j$, $i \in C_j$", which symmetrizes it.
-- source:
--   Aouad, Farias and Levi, Assortment Optimization Under Consider-then-Choose Choice Models, Management Science 67(6) (2021), doi:10.1287/mnsc.2020.3681 (accepted manuscript, LBS Research Online eprint 1426), §3 "Graph Representation", p. 11 (model: §2.1, p. 8; product renumbering: §3 "Preliminaries", p. 11)

import Mathlib

namespace ConsiderThenChoose

/-- **The bipartite graph `G = ([N], [K], E)` of an instance.** Aouad, Farias and Levi,
*Assortment Optimization Under Consider-then-Choose Choice Models*, Management Science 67(6)
(2021), doi:10.1287/mnsc.2020.3681, §3 "Graph Representation", unnumbered, p. 11:
"we define the graph G = ([N],[K],E), where E = {(i,j) ∈ [N] × [K] : i ∈ C_j}".

The vertices are the products `Sum.inl i` (`i : Fin N`) and the customer types `Sum.inr j`
(`j : Fin K`); product `i` and type `j` are adjacent exactly when `i ∈ C j`. There are no
product–product and no type–type edges.

**Formalization Note** Products are `Fin N`, 0-based and renumbered in preference order
(`0` is the paper's product 1, the most preferred; p. 11, "product 1 is the most preferred
one"). Types are `Fin K`, 0-based. `C j` is the consideration set of type `j`. The graph is
undirected (`SimpleGraph.fromRel` symmetrizes the relation). -/
def bipGraph {N K : ℕ} (C : Fin K → Finset (Fin N)) : SimpleGraph (Fin N ⊕ Fin K) :=
  SimpleGraph.fromRel fun v w => ∃ i j, v = Sum.inl i ∧ w = Sum.inr j ∧ i ∈ C j

end ConsiderThenChoose


