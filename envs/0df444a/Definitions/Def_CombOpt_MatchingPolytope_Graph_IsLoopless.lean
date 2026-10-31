-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_Graph_IsLoopless
-- name    : CombOpt_MatchingPolytope_Graph_IsLoopless
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:15.182775+00:00
-- url     : https://prove2.me/theorems/f84af66b-eee0-4d96-a870-17cf405aa305
-- title:
--   A graph without loops
-- statement:
--   A graph $G=(V,E)$ is **loopless** if no edge of $G$ is a loop, that is, every edge has two distinct ends. Parallel edges are still allowed.
--
--   This is the hypothesis under which the Matching Polytope Theorem (Theorem 6.20) and the Perfect Matching Polytope Theorem (Theorem 6.3) hold; both printed statements fail on a graph with a loop.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 9 (PDF p. 18)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph

namespace CombOpt.MatchingPolytope

/-- **G has no loops.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 9 (PDF p. 18): "an edge whose ends are the same is called a loop".

`G.IsLoopless` says that no edge of `G` is a loop; parallel edges remain allowed.

**Formalization Note.** This is the hypothesis of the corrected Matching Polytope Theorem
(Theorem 6.20, p. 214) and of the corrected Theorem 6.3 (p. 201): both printed statements fail
on a graph with a loop. -/
def Graph.IsLoopless {V E : Type*} (G : Graph V E) : Prop :=
  ∀ e : E, ¬ (G.ends e).IsDiag

end CombOpt.MatchingPolytope


