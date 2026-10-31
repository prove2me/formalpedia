-- Prove2me | Definitions.Def_CombOpt_ShortestPath_Digraph_IsFeasiblePotential
-- name    : CombOpt_ShortestPath_Digraph_IsFeasiblePotential
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:01.129287+00:00
-- url     : https://prove2.me/theorems/c0a3b202-b634-4e18-8f3c-b609b36dd365
-- title:
--   Feasible potential (root $r$)
-- statement:
--   Let $r\in V$ be the root of the shortest path problem. A real vector $y=(y_v:v\in V)$ is a **feasible potential** if it satisfies (2.12),
--   $$y_v+c_{vw}\ge y_w\quad(vw\in E),\qquad\text{and}\qquad y_r=0.$$
--
--   Feasible potentials give lower bounds on dipath costs (Proposition 2.9), and the largest value $y_s$ of a feasible potential equals the least cost of a dipath from $r$ to $s$ when least-cost dipaths exist (Theorem 2.14).
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 21 (PDF p. 30), definition of a feasible potential

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph_SatisfiesPotentialIneq

namespace CombOpt.ShortestPath

/-- **A feasible potential.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, p. 21 (PDF p. 30): "We call y = (y_v : v ∈ V) a *feasible potential* if it satisfies
(2.12) and y_r = 0."

`G.IsFeasiblePotential c r y` says that the real vector `y` satisfies (2.12) for every arc and
`y r = 0`, where `r` is the root node of the shortest path problem. -/
def Digraph.IsFeasiblePotential {V E : Type*} (G : Digraph V E) (c : E → ℝ) (r : V)
    (y : V → ℝ) : Prop :=
  G.SatisfiesPotentialIneq c y ∧ y r = 0

end CombOpt.ShortestPath


