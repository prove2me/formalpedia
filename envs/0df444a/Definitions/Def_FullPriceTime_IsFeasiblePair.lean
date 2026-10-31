-- Prove2me | Definitions.Def_FullPriceTime_IsFeasiblePair
-- name    : FullPriceTime_IsFeasiblePair
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:15.390989+00:00
-- url     : https://prove2.me/theorems/7fdc2745-3426-4a6e-beb2-6ac504449d14
-- title:
--   Feasible price–time pair $(r,\delta)$
-- statement:
--   A price $r$ and a time commitment $\delta$ of the discrete service are **feasible** when the buyer's problem has a non-empty feasible set: there is a plan $(t_l,c_l,t_w,c_O)$ that is feasible for (PC) with the purchase decision $y=1$.
--
--   **Formalization Note** The constraints are those of a buyer ($y=1$); with $y=0$ the pair $(r,\delta)$ does not enter (PC), and the paper uses feasibility of $(r,\delta)$ only for the buyer's utility $u^B$.
-- source:
--   Li, Lariviere, Bassamboo, Is Full Price the Full Story When Consumers Have Time and Budget Constraints?, SSRN 4223388, §2.2, p.7

import Mathlib
import Definitions.Def_FullPriceTime_IsFeasiblePlan

namespace FullPriceTime

/-- **Feasible price–time pair `(r, δ)`.**
Li, Lariviere, Bassamboo, *Is Full Price the Full Story When Consumers Have Time and Budget
Constraints?*, SSRN 4223388, §2.2, p.7 (PDF p.7): "we say that a discrete service price r and time
commitment δ are feasible if there exist non-negative tl, tw, cl, and cO that satisfy the
constraints of (PC), i.e., (PC) has a non-empty feasible set."

`IsFeasiblePair T O comp r δ` holds when some plan is feasible for (PC) with the purchase decision
`y = 1`.

**Formalization Note** The constraints are those of a buyer (`y = 1`): with `y = 0` the price and
the time commitment do not enter (PC), and the notion is used on p.7 only for the buyer's utility
`u^B`. -/
def IsFeasiblePair (T : ℝ) (O : ℝ → ℝ) (comp : ℝ → ℝ) (r δ : ℝ) : Prop :=
  ∃ p : Plan, IsFeasiblePlan T O comp r δ 1 p

end FullPriceTime


