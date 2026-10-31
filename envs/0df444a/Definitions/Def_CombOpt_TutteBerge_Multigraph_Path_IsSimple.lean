-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsSimple
-- name    : CombOpt_TutteBerge_Multigraph_Path_IsSimple
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:50.217065+00:00
-- url     : https://prove2.me/theorems/902446c8-4864-46d6-b6dd-4d8fd9175c54
-- title:
--   Simple path
-- statement:
--   A path is **simple** if its nodes $v_0,\dots,v_k$ are distinct.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_nodes

namespace CombOpt.TutteBerge

/-- **A simple path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): "it is *simple* if v₀, …, v_k are distinct". -/
def Multigraph.Path.IsSimple {V E : Type*} {G : Multigraph V E} {u w : V} (P : G.Path u w) : Prop :=
  P.nodes.Nodup

end CombOpt.TutteBerge


