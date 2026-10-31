-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_edges
-- name    : CombOpt_TutteBerge_Multigraph_Path_edges
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:06.729746+00:00
-- url     : https://prove2.me/theorems/78be4d42-89be-4d42-8b7c-d156eeab5275
-- title:
--   The edge sequence of a path
-- statement:
--   The list $e_1,\dots,e_k$ of edges of the path $v_0,e_1,v_1,\dots,e_k,v_k$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path

namespace CombOpt.TutteBerge

/-- **The edge sequence e₁, …, e_k of a path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19). -/
def Multigraph.Path.edges {V E : Type*} {G : Multigraph V E} {u w : V} :
    G.Path u w → List E
  | .nil _ => []
  | .cons e _ p => e :: p.edges

end CombOpt.TutteBerge


