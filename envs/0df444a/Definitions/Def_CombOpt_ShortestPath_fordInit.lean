-- Prove2me | Definitions.Def_CombOpt_ShortestPath_fordInit
-- name    : CombOpt_ShortestPath_fordInit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:35.090926+00:00
-- url     : https://prove2.me/theorems/f2f0205b-8591-488e-8d9f-2b0609f77087
-- title:
--   Initialization of Ford's Algorithm
-- statement:
--   To **initialize** $y$ and $p$ means to set
--   $$y_r=0,\quad p(r)=0,\qquad y_v=\infty,\quad p(v)=-1\quad(v\in V\setminus\{r\}).$$
--   This is the starting state of every execution of Ford's Algorithm.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 22 (PDF p. 31), initialization

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_FordState

namespace CombOpt.ShortestPath

/-- **Initialization of Ford's Algorithm.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, p. 22 (PDF p. 31): "To *initialize* y and p means to set y_r = 0, p(r) = 0, y_v = ∞
and p(v) = −1 for v ∈ V∖{r}."

`fordInit r` has `y r = 0`, `p r = root`, and `y v = ⊤`, `p v = undef` for `v ≠ r`. -/
def fordInit {V E : Type*} [DecidableEq V] (r : V) : FordState V E where
  y := fun v => if v = r then 0 else ⊤
  p := fun v => if v = r then FordPred.root else FordPred.undef

end CombOpt.ShortestPath


