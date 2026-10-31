-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_nodeSet
-- name    : CombOpt_TutteBerge_Multigraph_Path_nodeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:12.937069+00:00
-- url     : https://prove2.me/theorems/65ed42ca-5273-4d43-a3e7-bcef6462381e
-- title:
--   $V(C)$: the nodes of a path
-- statement:
--   For a path $C$, the set $V(C)$ of nodes occurring in it.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 131 (PDF p. 139)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_nodes

namespace CombOpt.TutteBerge

/-- **V(C), the set of nodes of a path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 131 (PDF p. 139), where V(C) is the node set of the circuit C. -/
def Multigraph.Path.nodeSet {V E : Type*} {G : Multigraph V E} {u w : V} (P : G.Path u w) : Set V :=
  {v | v ∈ P.nodes}

end CombOpt.TutteBerge


