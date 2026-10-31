-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_exposedNodes
-- name    : CombOpt_TutteBerge_Multigraph_exposedNodes
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:52.289999+00:00
-- url     : https://prove2.me/theorems/9f2b15e3-2c11-477e-b624-6ac3e38dae42
-- title:
--   The $M$-exposed nodes
-- statement:
--   For $M\subseteq E$, a node is **$M$-exposed** if $M$ does not cover it. This is the set of $M$-exposed nodes of $G$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Covers

namespace CombOpt.TutteBerge

/-- **The `M`-exposed nodes.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 127 (PDF p. 135): "Otherwise, v is *M-exposed*."

The set of nodes not covered by `M`. -/
def Multigraph.exposedNodes {V E : Type*} (G : Multigraph V E) (M : Set E) : Set V :=
  {v | ¬ G.Covers M v}

end CombOpt.TutteBerge


