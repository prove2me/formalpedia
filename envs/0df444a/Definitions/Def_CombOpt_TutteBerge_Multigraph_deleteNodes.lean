-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_deleteNodes
-- name    : CombOpt_TutteBerge_Multigraph_deleteNodes
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:17.358751+00:00
-- url     : https://prove2.me/theorems/0422b269-c51c-4bc5-8c79-91646b05a9e1
-- title:
--   The subgraph $G\setminus A$
-- statement:
--   For $A\subseteq V$, the subgraph $G\setminus A$ has node set $V\setminus A$ and consists of the edges of $G$ with no end in $A$, each with the same ends as in $G$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph

namespace CombOpt.TutteBerge

/-- **The subgraph G\A obtained by deleting a set of nodes.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): "we can delete a subset B of V, if we also delete all edges incident
with nodes in B. The resulting subgraph is denoted by G\B or by G[V\B]".

The nodes are those outside `A`, the edges are those with no end in `A`, and each edge keeps its
ends. -/
def Multigraph.deleteNodes {V E : Type*} (G : Multigraph V E) (A : Set V) :
    Multigraph {v : V // v ∉ A} {e : E // ∀ v ∈ G.ends e, v ∉ A} where
  ends e := (G.ends e.1).pmap (fun v hv => ⟨v, hv⟩) e.2

end CombOpt.TutteBerge


