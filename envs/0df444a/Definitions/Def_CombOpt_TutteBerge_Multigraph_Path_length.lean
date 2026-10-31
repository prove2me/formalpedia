-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_length
-- name    : CombOpt_TutteBerge_Multigraph_Path_length
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:32.166213+00:00
-- url     : https://prove2.me/theorems/bfea11e8-2a0a-43a7-a149-b8b509e5ed31
-- title:
--   The length of a path
-- statement:
--   The **length** of a path is $k$, the number of its edge terms.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_edges

namespace CombOpt.TutteBerge

/-- **The length of a path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19): "The *length* of P is k, the number of edge-terms of P." -/
def Multigraph.Path.length {V E : Type*} {G : Multigraph V E} {u w : V} (P : G.Path u w) : ℕ :=
  P.edges.length

end CombOpt.TutteBerge


