-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_edgeSet
-- name    : CombOpt_TutteBerge_Multigraph_Path_edgeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:11.171519+00:00
-- url     : https://prove2.me/theorems/67a0da00-22f8-4ad6-8004-0fdcd4ed27b1
-- title:
--   $E(C)$: the edges of a path
-- statement:
--   For a path $C$, the set $E(C)$ of edges occurring in it.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 131 (PDF p. 139)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_edges

namespace CombOpt.TutteBerge

/-- **E(C), the set of edges of a path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 131 (PDF p. 139), where E(C) is the edge set of the circuit C. -/
def Multigraph.Path.edgeSet {V E : Type*} {G : Multigraph V E} {u w : V} (P : G.Path u w) : Set E :=
  {e | e ∈ P.edges}

end CombOpt.TutteBerge


