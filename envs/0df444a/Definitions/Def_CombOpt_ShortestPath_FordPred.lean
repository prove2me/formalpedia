-- Prove2me | Definitions.Def_CombOpt_ShortestPath_FordPred
-- name    : CombOpt_ShortestPath_FordPred
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:23.394848+00:00
-- url     : https://prove2.me/theorems/66311a36-439e-445b-96a3-e9c22275ca3a
-- title:
--   Predecessor labels $p(v)$ of Ford's Algorithm
-- statement:
--   Ford's Algorithm keeps a **predecessor** $p(w)$ for each node $w$. It takes one of three kinds of values:
--
--   1. $0$, given to the root $r$ at initialization;
--   2. $-1$, meaning that the predecessor of $w$ is not (yet) defined;
--   3. a node $v$, set when the arc $vw$ is corrected.
--
--   **Formalization Note** The three kinds are the constructors `root`, `undef` and `arc e`. The third stores the corrected arc $e=vw$ rather than its tail $v$; on a simple digraph these carry the same information, and storing the arc still determines the dipath when there are parallel arcs.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 22 (PDF p. 31), predecessors and initialization

import Mathlib

namespace CombOpt.ShortestPath

/-- **Values of the predecessor label p(v) in Ford's Algorithm.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, p. 22 (PDF p. 31): "we keep a 'predecessor' p(w) for each w ∈ V and set p(w) to v
whenever y_w is set to y_v + c_vw. … To *initialize* y and p means to set y_r = 0, p(r) = 0,
y_v = ∞ and p(v) = −1 for v ∈ V∖{r}. (We are using p(v) = −1 to mean that the predecessor of v
is not (yet) defined, but we want to distinguish r from such nodes. We are assuming that
0, −1 ∉ V.)"

`root` is the book's label `0` (given to `r` at initialization), `undef` is the book's
label `−1`, and `arc e` records that the label was last set by correcting the arc `e`.

**Formalization Note.** The book stores the node `v = t(e)` in `p(w)`; here the arc `e = vw`
itself is stored, which carries the same information on a simple digraph (the book's
standing simplification, p. 20) and still determines the dipath when there are parallel arcs. -/
inductive FordPred (E : Type*) where
  /-- The label `0` of the root `r`. -/
  | root : FordPred E
  /-- The label `−1`: no predecessor defined yet. -/
  | undef : FordPred E
  /-- The predecessor was set by correcting the arc `e` (book: `p(h(e)) = t(e)`). -/
  | arc (e : E) : FordPred E

end CombOpt.ShortestPath


