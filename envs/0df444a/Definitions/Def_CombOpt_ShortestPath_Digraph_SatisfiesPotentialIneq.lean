-- Prove2me | Definitions.Def_CombOpt_ShortestPath_Digraph_SatisfiesPotentialIneq
-- name    : CombOpt_ShortestPath_Digraph_SatisfiesPotentialIneq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:03.456457+00:00
-- url     : https://prove2.me/theorems/ddeaa27b-e1bc-4670-b1da-7aa209a20850
-- title:
--   The potential inequalities (2.12)
-- statement:
--   A real vector $y=(y_v:v\in V)$ satisfies **(2.12)** if
--   $$y_v+c_{vw}\ \ge\ y_w\qquad\text{for all } vw\in E,$$
--   that is, $y_{h(e)}\le y_{t(e)}+c_e$ for every arc $e$ (loops and parallel arcs included).
--
--   If $y_v$ is the least cost of a dipath from $r$ to $v$ for every $v$, then $y$ satisfies (2.12); conversely (2.12) is the stopping condition of Ford's Algorithm.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 20 (PDF p. 29), inequality (2.12)

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph

namespace CombOpt.ShortestPath

/-- **The potential inequalities (2.12).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, p. 20 (PDF p. 29), (2.12): "y_v + c_vw ≥ y_w, for all vw ∈ E."

`G.SatisfiesPotentialIneq c y` says that `y (tail e) + c e ≥ y (head e)` for every arc `e`
(the book writes `e = vw` for an arc with tail `v` and head `w`, p. 19). -/
def Digraph.SatisfiesPotentialIneq {V E : Type*} (G : Digraph V E) (c : E → ℝ) (y : V → ℝ) :
    Prop :=
  ∀ e : E, y (G.head e) ≤ y (G.tail e) + c e

end CombOpt.ShortestPath


