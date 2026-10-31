-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph_IsSpanningTree
-- name    : CombOpt_SpanningTree_Graph_IsSpanningTree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:26.228299+00:00
-- url     : https://prove2.me/theorems/98d314e8-edc2-4d8a-a6a6-195a81905fac
-- title:
--   Spanning tree
-- statement:
--   A set $T\subseteq E$ of edges is (the edge set of) a **spanning tree** of $G$ if the spanning subgraph $(V,T)$ is connected and is a forest ("a connected forest is called a tree").
--
--   **Formalization Note** A spanning subgraph is determined by its edge set, so a spanning tree is recorded as a `Finset E`.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 11 (PDF p. 20)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_SpanConnected
import Definitions.Def_CombOpt_SpanningTree_Graph_IsForest

namespace CombOpt.SpanningTree

/-- **T is (the edge set of) a spanning tree.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 11 (PDF p. 20): "a connected forest is called a tree"; a subgraph is spanning if it
has all the nodes of G (p. 10).

`G.IsSpanningTree T` says that the spanning subgraph `(V, T)` is connected and has no circuit.

**Formalization Note.** A spanning subgraph is determined by its edge set `T ⊆ E`, so a spanning
tree is recorded as a `Finset E`. -/
def Graph.IsSpanningTree {V E : Type*} (G : Graph V E) (T : Finset E) : Prop :=
  G.SpanConnected T ∧ G.IsForest T

end CombOpt.SpanningTree


