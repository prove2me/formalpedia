-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsAlternating
-- name    : CombOpt_TutteBerge_Multigraph_Path_IsAlternating
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:02.395024+00:00
-- url     : https://prove2.me/theorems/08d5d4a3-c6f7-4071-8950-55625fa0bac9
-- title:
--   $M$-alternating path
-- statement:
--   A path is **$M$-alternating** if its edges are alternately in and not in $M$: of any two consecutive edges of the path, exactly one lies in $M$. The type of the first and of the last edge is not specified.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 128 (PDF p. 136)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_edges

namespace CombOpt.TutteBerge

/-- **An `M`-alternating path.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 128 (PDF p. 136): "a path P is *M-alternating* if its edges are alternately in and
not in M. (Note that we do not specify the type of the first and last edges of P.)"

Of any two consecutive edges of `P`, exactly one lies in `M`. A path with at most one edge is
alternating. -/
def Multigraph.Path.IsAlternating {V E : Type*} {G : Multigraph V E} {u w : V} (P : G.Path u w)
    (M : Set E) : Prop :=
  P.edges.IsChain (fun e f => (e ∈ M ∧ f ∉ M) ∨ (e ∉ M ∧ f ∈ M))

end CombOpt.TutteBerge


