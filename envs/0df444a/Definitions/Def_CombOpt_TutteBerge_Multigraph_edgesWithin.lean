-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_edgesWithin
-- name    : CombOpt_TutteBerge_Multigraph_edgesWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:15.975961+00:00
-- url     : https://prove2.me/theorems/dddcf3ed-87f6-429b-8362-6c24c6403b5b
-- title:
--   $\gamma(S)$: the edges inside a node set
-- statement:
--   For $S\subseteq V$, $\gamma(S)$ is the set of edges of $G$ with both ends in $S$. Loops at nodes of $S$ belong to it.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 131 (PDF p. 139)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph

namespace CombOpt.TutteBerge

/-- **γ(S), the edges with both ends in `S`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 131 (PDF p. 139), which uses γ(V(C)); the notation is the book's, "γ(A)" being the
set of edges with both ends in A. Loops at nodes of `S` are included. -/
def Multigraph.edgesWithin {V E : Type*} (G : Multigraph V E) (S : Set V) : Set E :=
  {e | ∀ v ∈ G.ends e, v ∈ S}

end CombOpt.TutteBerge


