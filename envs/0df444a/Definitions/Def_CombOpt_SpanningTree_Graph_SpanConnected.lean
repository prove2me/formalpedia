-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph_SpanConnected
-- name    : CombOpt_SpanningTree_Graph_SpanConnected
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:47.446395+00:00
-- url     : https://prove2.me/theorems/fa6c71d1-9657-429f-99c4-c1a64d5ac541
-- title:
--   The spanning subgraph $(V,F)$ is connected
-- statement:
--   For a set $F\subseteq E$ of edges, the **spanning subgraph** $(V,F)$ has all nodes of $G$ and the edges of $F$, with their ends in $G$. It is **connected** if every pair of nodes $u,v$ is joined by a path all of whose edges lie in $F$.
--
--   The graph $G$ itself is connected when $(V,E)$ is.
--
--   **Formalization Note** A spanning subgraph is identified with its edge set `F : Finset E`; $G$ is connected when `G.SpanConnected Finset.univ`. With no nodes the condition holds vacuously, as in the book's definition.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_Walk_edges

namespace CombOpt.SpanningTree

/-- **The spanning subgraph (V, F) is connected.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): "The graph G is connected if every pair of nodes is joined by a
path"; a subgraph H of G is spanning if V(H) = V(G), and "given a graph G and subsets P of nodes
and Q of edges, we may refer unambiguously to 'the subgraph (P, Q) of G'".

`G.SpanConnected F` says that the spanning subgraph `(V, F)` is connected: for all nodes `u, v`
there is a path from `u` to `v` all of whose edges lie in `F`. The graph `G` itself is connected
when `G.SpanConnected Finset.univ`.

**Formalization Note.** A path of the subgraph `(V, F)` is a path of `G` using only edges of `F`
(a subgraph keeps the ends of its edges). With no nodes the condition holds vacuously, as the
book's definition reads. -/
def Graph.SpanConnected {V E : Type*} (G : Graph V E) (F : Finset E) : Prop :=
  ∀ u v : V, ∃ p : G.Walk u v, ∀ e ∈ p.edges, e ∈ F

end CombOpt.SpanningTree


