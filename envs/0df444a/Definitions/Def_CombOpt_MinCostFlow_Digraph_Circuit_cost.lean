-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph_Circuit_cost
-- name    : CombOpt_MinCostFlow_Digraph_Circuit_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:00.998481+00:00
-- url     : https://prove2.me/theorems/23b8ecb9-3279-454e-ada2-4964eb450d00
-- title:
--   Cost of a circuit
-- statement:
--   The **cost** of a circuit $C$ with respect to $c\in\mathbb R^E$ is
--
--   $$\sum(c_e : e\text{ forward in }C)-\sum(c_e : e\text{ reverse in }C).$$
--
--   Sending $\varepsilon$ units of flow around an $x$-incrementing circuit changes the cost $c^\top x$ by $\varepsilon$ times this number.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §4.1, p. 93 (PDF p. 101)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_Circuit

namespace CombOpt.MinCostFlow

/-- **Cost of a circuit.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §4.1, p. 93 (PDF p. 101): "Given a path P in G, not necessarily directed, we define the
cost (with respect to c) of P to be Σ(c_e : e forward in P) − Σ(c_e : e reverse in P)." -/
def Digraph.Circuit.cost {V E : Type*} {G : Digraph V E} (C : G.Circuit) (c : E → ℝ) : ℝ :=
  ∑ i, if C.forward i then c (C.arc i) else -c (C.arc i)

end CombOpt.MinCostFlow


