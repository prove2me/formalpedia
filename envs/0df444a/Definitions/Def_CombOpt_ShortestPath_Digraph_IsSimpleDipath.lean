-- Prove2me | Definitions.Def_CombOpt_ShortestPath_Digraph_IsSimpleDipath
-- name    : CombOpt_ShortestPath_Digraph_IsSimpleDipath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:49.191448+00:00
-- url     : https://prove2.me/theorems/68e26b26-6d6c-430e-8069-c2aef1e5f2d7
-- title:
--   Simple dipath (distinct nodes)
-- statement:
--   A dipath $v_0,e_1,v_1,\dots,e_k,v_k$ is **simple** if its nodes $v_0,v_1,\dots,v_k$ are pairwise distinct.
--
--   Simple dipaths appear in the invariants of Ford's Algorithm (Proposition 2.10): every finite label is the cost of a simple dipath.
--
--   **Formalization Note** In the arc-list representation the nodes are $u,h(e_1),\dots,h(e_k)$, and simplicity is `List.Nodup` of this list.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19), simple paths

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsDipath

namespace CombOpt.ShortestPath

/-- **A simple dipath.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): a path v_0, e_1, v_1, …, e_k, v_k "is *simple* if v_0, …, v_k are
distinct".

`G.IsSimpleDipath u P v` says `P` is a dipath from `u` to `v` whose nodes
`u, head e_1, …, head e_k` are pairwise distinct. -/
def Digraph.IsSimpleDipath {V E : Type*} (G : Digraph V E) (u : V) (P : List E) (v : V) : Prop :=
  G.IsDipath u P v ∧ (u :: P.map G.head).Nodup

end CombOpt.ShortestPath


