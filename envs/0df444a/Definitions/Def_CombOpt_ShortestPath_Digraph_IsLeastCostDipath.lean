-- Prove2me | Definitions.Def_CombOpt_ShortestPath_Digraph_IsLeastCostDipath
-- name    : CombOpt_ShortestPath_Digraph_IsLeastCostDipath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:21.693546+00:00
-- url     : https://prove2.me/theorems/c1462e9e-038a-44d3-8d9a-07c45be77e56
-- title:
--   Least-cost dipath from $u$ to $v$
-- statement:
--   A dipath $P$ from $u$ to $v$ is a **least-cost dipath** if $c(P)\le c(Q)$ for every dipath $Q$ from $u$ to $v$, simple or not.
--
--   The Shortest Path Problem asks, for a root $r$ and each node $v$, for a least-cost dipath from $r$ to $v$ (if one exists). None exists when $v$ is not reachable from $r$, or when arbitrarily cheap dipaths to $v$ exist because of a negative-cost closed dipath.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 20 (PDF p. 29), Shortest Path Problem

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsDipath
import Definitions.Def_CombOpt_ShortestPath_pathCost

namespace CombOpt.ShortestPath

/-- **A least-cost dipath.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, p. 20 (PDF p. 29), Shortest Path Problem: "to find, for each v ∈ V, a dipath from r
to v of least cost (if one exists)".

`G.IsLeastCostDipath c u v P` says that `P` is a dipath from `u` to `v` and no dipath from
`u` to `v` (simple or not) has smaller cost. -/
def Digraph.IsLeastCostDipath {V E : Type*} (G : Digraph V E) (c : E → ℝ) (u v : V)
    (P : List E) : Prop :=
  G.IsDipath u P v ∧ ∀ Q : List E, G.IsDipath u Q v → pathCost c P ≤ pathCost c Q

end CombOpt.ShortestPath


