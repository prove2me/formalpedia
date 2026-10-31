-- Prove2me | Definitions.Def_CombOpt_ShortestPath_Digraph_fordCorrect
-- name    : CombOpt_ShortestPath_Digraph_fordCorrect
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:48.392958+00:00
-- url     : https://prove2.me/theorems/745cdeb9-03d2-416c-b364-d90419fd80cb
-- title:
--   Correcting an arc
-- statement:
--   To **correct** an arc $vw$ means to set
--   $$y_w:=y_v+c_{vw}\qquad\text{and}\qquad p(w):=v,$$
--   leaving all other labels unchanged.
--
--   **Formalization Note** The predecessor of $w$ records the arc $e=vw$ itself (see the predecessor labels).
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 22 (PDF p. 31), correcting an arc

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph
import Definitions.Def_CombOpt_ShortestPath_FordState

namespace CombOpt.ShortestPath

/-- **Correcting an arc.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, p. 22 (PDF p. 31): "To *correct* vw means to set y_w = y_v + c_vw and to set
p(w) = v."

`G.fordCorrect c s e` is the state `s` with `y (head e)` replaced by
`y (tail e) + c e` and `p (head e)` replaced by `arc e`; all other labels are unchanged.

**Formalization Note.** `p` records the arc `e` rather than its tail (see `FordPred`). -/
def Digraph.fordCorrect {V E : Type*} [DecidableEq V] (G : Digraph V E) (c : E → ℝ)
    (s : FordState V E) (e : E) : FordState V E where
  y := Function.update s.y (G.head e) (s.y (G.tail e) + ((c e : ℝ) : WithTop ℝ))
  p := Function.update s.p (G.head e) (FordPred.arc e)

end CombOpt.ShortestPath


