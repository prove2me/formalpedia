-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_nodes
-- name    : CombOpt_TutteBerge_Multigraph_Path_nodes
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:56.798447+00:00
-- url     : https://prove2.me/theorems/c971c1e3-7510-41ff-adb2-4c1955ab7a8d
-- title:
--   The node sequence of a path
-- statement:
--   The list $v_0,\dots,v_k$ of nodes of the path $v_0,e_1,v_1,\dots,e_k,v_k$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path

namespace CombOpt.TutteBerge

/-- **The node sequence v₀, …, v_k of a path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19). -/
def Multigraph.Path.nodes {V E : Type*} {G : Multigraph V E} {u w : V} :
    G.Path u w → List V
  | .nil v => [v]
  | @Multigraph.Path.cons _ _ _ u _ _ _ _ p => u :: p.nodes

end CombOpt.TutteBerge


