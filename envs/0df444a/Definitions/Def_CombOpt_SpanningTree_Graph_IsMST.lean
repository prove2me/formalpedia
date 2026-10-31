-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph_IsMST
-- name    : CombOpt_SpanningTree_Graph_IsMST
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:28.439115+00:00
-- url     : https://prove2.me/theorems/a1d539ae-2a08-43b7-9f30-e7475afbca86
-- title:
--   Minimum spanning tree (MST)
-- statement:
--   Let $c\in\mathbb R^E$ be real edge costs (negative costs allowed). The cost of an edge set $T$ is $c(T)=\sum_{e\in T}c_e$. A spanning tree $T$ of $G$ is a **minimum spanning tree (MST)** if
--   $$c(T)\le c(T')\quad\text{for every spanning tree } T' \text{ of } G.$$
--
--   An MST exists exactly when $G$ has a spanning tree, i.e. when $G$ is connected.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 11 (PDF p. 20), Minimum Spanning Tree Problem

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsSpanningTree

namespace CombOpt.SpanningTree

/-- **T is a minimum spanning tree (MST) for the edge costs c.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 11 (PDF p. 20): "Minimum Spanning Tree Problem. Given a connected graph G and a
real cost c_e for each e ∈ E, find a minimum cost spanning tree of G", where (p. 10) "the cost of
a subgraph is the sum of the costs of its edges".

`G.IsMST c T` says that `T` is a spanning tree and `∑_{e ∈ T} c e ≤ ∑_{e ∈ T'} c e` for every
spanning tree `T'`.

**Formalization Note.** Costs are arbitrary reals (negative allowed, as the book allows for the
MST problem). An MST exists exactly when G has a spanning tree, i.e. when G is connected; no
connectivity hypothesis is built in. -/
def Graph.IsMST {V E : Type*} (G : Graph V E) (c : E → ℝ) (T : Finset E) : Prop :=
  G.IsSpanningTree T ∧ ∀ T' : Finset E, G.IsSpanningTree T' → ∑ e ∈ T, c e ≤ ∑ e ∈ T', c e

end CombOpt.SpanningTree


