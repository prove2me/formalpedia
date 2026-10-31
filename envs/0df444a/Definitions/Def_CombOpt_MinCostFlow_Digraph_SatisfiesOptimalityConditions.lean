-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph_SatisfiesOptimalityConditions
-- name    : CombOpt_MinCostFlow_Digraph_SatisfiesOptimalityConditions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:50.248807+00:00
-- url     : https://prove2.me/theorems/3d6d0152-fd94-4294-ab90-66e4eb59db62
-- title:
--   Reduced-cost optimality conditions of Theorem 4.1
-- statement:
--   Let $G$ be a digraph with capacities $u$, costs $c$, a flow $x$ and a node vector $y$, and let $\bar c$ be the reduced cost with respect to $y$. The pair $(x,y)$ satisfies the **optimality conditions** when, for every arc $e$,
--
--   1. $\bar c_e<0$ implies $u_e\neq\infty$ and $x_e=u_e$;
--   2. $\bar c_e>0$ implies $x_e=0$.
--
--   These are the conditions of Theorem 4.1; they are the complementary slackness conditions for the pair (4.1), (4.3).
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 4.1, p. 93 (PDF p. 101)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_reducedCost

namespace CombOpt.MinCostFlow

/-- **The reduced-cost optimality conditions of Theorem 4.1.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 4.1, p. 93 (PDF p. 101): for each e ∈ E,
"c̄_e < 0 implies x_e = u_e (≠ ∞)" and "c̄_e > 0 implies x_e = 0".

`G.SatisfiesOptimalityConditions u c x y` holds when for every arc `e`: if `c̄_e < 0` then `u e`
is finite and `x e = u e`, and if `c̄_e > 0` then `x e = 0`, where `c̄` is the reduced cost with
respect to `y`.

**Formalization Note.** The parenthesis "(≠ ∞)" is part of the condition: `u e ≠ ⊤`. -/
def Digraph.SatisfiesOptimalityConditions {V E : Type*} (G : Digraph V E) (u : E → EReal)
    (c : E → ℝ) (x : E → ℝ) (y : V → ℝ) : Prop :=
  ∀ e, (G.reducedCost c y e < 0 → u e ≠ ⊤ ∧ (x e : EReal) = u e) ∧
    (0 < G.reducedCost c y e → x e = 0)

end CombOpt.MinCostFlow


