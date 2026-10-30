-- Prove2me | Definitions.Def_CommissionsSubscriptions_IsOptimal7
-- name    : CommissionsSubscriptions_IsOptimal7
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:32:38.04142+00:00
-- url     : https://prove2.me/theorems/a85783cb-a356-4c3f-81a8-b9507bd5e9dc
-- title:
--   Optimal solution of the relaxation (7)
-- statement:
--   A triple $(\bar x,\bar q^s,\bar q^b)$ is an **optimal solution of (7)** if it is feasible in (7) and
--   $$h(q^s,q^b)\le h(\bar q^s,\bar q^b)\quad\text{for every feasible }(x,q^s,q^b).$$
--   Its value $h(\bar q^s,\bar q^b)$ is $\tilde V_{opt}$. Problem (7) is a min-cost network flow problem with convex edge costs, and under Assumption 2 a convex program.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), (7a)–(7f), p. 12

import Mathlib
import Definitions.Def_CommissionsSubscriptions_obj7
import Definitions.Def_CommissionsSubscriptions_Feasible7

namespace CommissionsSubscriptions

/-- **An optimal solution `(x̄, q̄^s, q̄^b)` of the relaxation (7).**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), (7a)–(7f), p. 12: feasible for (7b)–(7f), and its
objective value (7a) is at least that of every feasible point. `Ṽ_opt` is then
`obj7 M q̄s q̄b`. -/
def IsOptimal7 {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) : Prop :=
  Feasible7 M x qs qb ∧
    ∀ (x' : S → B → ℝ) (qs' : S → ℝ) (qb' : B → ℝ),
      Feasible7 M x' qs' qb' → obj7 M qs' qb' ≤ obj7 M qs qb

end CommissionsSubscriptions


