-- Prove2me | Definitions.Def_CombOpt_ShortestPath_Digraph_HasNegativeDicircuit
-- name    : CombOpt_ShortestPath_Digraph_HasNegativeDicircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:03:00.714707+00:00
-- url     : https://prove2.me/theorems/5f1489cf-90ce-4011-9749-fd72e6905805
-- title:
--   $(G,c)$ has a negative-cost dicircuit
-- statement:
--   The pair $(G,c)$ of a digraph and real arc costs **has a negative-cost dicircuit** if some dicircuit $C$ of $G$ has $c(C)<0$.
--
--   Its negation, "$(G,c)$ has no negative-cost dicircuit", is the hypothesis under which Ford's Algorithm is valid (Proposition 2.10, Theorem 2.11) and the condition characterizing the existence of feasible potentials (Theorem 2.12).
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.2, pp. 23–25 (PDF pp. 32–34), Proposition 2.10, Theorems 2.11 and 2.12

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsDicircuit
import Definitions.Def_CombOpt_ShortestPath_pathCost

namespace CombOpt.ShortestPath

/-- **(G, c) has a negative-cost dicircuit.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.2, pp. 23–25 (PDF pp. 32–34): "(G, c) has no negative-cost dicircuit" is the hypothesis
of Proposition 2.10 and Theorems 2.11, 2.12.

`G.HasNegativeDicircuit c` holds when some dicircuit of `G` has cost `< 0` with respect to
the arc costs `c`. -/
def Digraph.HasNegativeDicircuit {V E : Type*} (G : Digraph V E) (c : E → ℝ) : Prop :=
  ∃ (u : V) (P : List E), G.IsDicircuit u P ∧ pathCost c P < 0

end CombOpt.ShortestPath


