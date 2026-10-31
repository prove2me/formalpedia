-- Prove2me | Definitions.Def_CombOpt_ShortestPath_Digraph_FordStep
-- name    : CombOpt_ShortestPath_Digraph_FordStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:09.667978+00:00
-- url     : https://prove2.me/theorems/96a4e4d6-c3da-4382-a74b-0da24e67e8a7
-- title:
--   One iteration of Ford's Algorithm
-- statement:
--   **Ford's Algorithm** is: initialize $y,p$; while $y$ is not a feasible potential, find an incorrect arc $vw$ and correct it.
--
--   One **iteration** turns a state $s$ into a state $s'$ when some arc $e$ is incorrect in $s$ and $s'$ is obtained from $s$ by correcting $e$. The arc may be any incorrect arc, so the algorithm is a nondeterministic process; a state with no incorrect arc admits no iteration.
--
--   **Formalization Note** The loop guard is read as "some arc is incorrect", because the body cannot be executed otherwise. Theorem 2.11 shows that under its hypotheses a reachable state without incorrect arcs carries a feasible potential, so both guards stop at the same states.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, p. 22 (PDF p. 31), Ford's Algorithm

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsIncorrect
import Definitions.Def_CombOpt_ShortestPath_Digraph_fordCorrect

namespace CombOpt.ShortestPath

/-- **One iteration of Ford's Algorithm.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, p. 22 (PDF p. 31):

  Ford's Algorithm
  Initialize y, p;
  While y is not a feasible potential
    Find an incorrect arc vw and correct it.

`G.FordStep c s s'` says that some arc `e` is incorrect in `s` and `s'` is obtained from `s`
by correcting `e`. The choice of the arc is arbitrary, so the algorithm is a nondeterministic
transition relation; a state with no incorrect arc is terminal.

**Formalization Note.** The loop guard is read as "some arc is incorrect": the iteration body can
only be executed when an incorrect arc exists, and Theorem 2.11
(`theorem_2_11`) asserts that, under its hypotheses, every terminal reachable state is a
feasible potential, so the two guards stop at the same states. -/
def Digraph.FordStep {V E : Type*} [DecidableEq V] (G : Digraph V E) (c : E → ℝ)
    (s s' : FordState V E) : Prop :=
  ∃ e : E, G.IsIncorrect c s.y e ∧ s' = G.fordCorrect c s e

end CombOpt.ShortestPath


