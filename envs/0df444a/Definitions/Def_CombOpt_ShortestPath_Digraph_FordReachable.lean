-- Prove2me | Definitions.Def_CombOpt_ShortestPath_Digraph_FordReachable
-- name    : CombOpt_ShortestPath_Digraph_FordReachable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:50.20845+00:00
-- url     : https://prove2.me/theorems/2770e392-8617-4ab5-8713-39b715d9824b
-- title:
--   A stage of an execution of Ford's Algorithm
-- statement:
--   A state $s$ is reached **at some stage of the execution** of Ford's Algorithm (with root $r$) if it is obtained from the initial state by finitely many iterations, zero included, each correcting some incorrect arc, in any order.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 24 (PDF p. 33), Proposition 2.10

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_fordInit
import Definitions.Def_CombOpt_ShortestPath_Digraph_FordStep

namespace CombOpt.ShortestPath

/-- **A stage of an execution of Ford's Algorithm.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, p. 24 (PDF p. 33), Proposition 2.10: "at any stage of the execution of Ford's
Algorithm".

`G.FordReachable c r s` says that `s` is obtained from the initial state `fordInit r` by
finitely many (possibly zero) iterations `FordStep`, each correcting some incorrect arc. -/
def Digraph.FordReachable {V E : Type*} [DecidableEq V] (G : Digraph V E) (c : E → ℝ) (r : V)
    (s : FordState V E) : Prop :=
  Relation.ReflTransGen (G.FordStep c) (fordInit r) s

end CombOpt.ShortestPath


