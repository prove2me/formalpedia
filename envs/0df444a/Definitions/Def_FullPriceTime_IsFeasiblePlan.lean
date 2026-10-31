-- Prove2me | Definitions.Def_FullPriceTime_IsFeasiblePlan
-- name    : FullPriceTime_IsFeasiblePlan
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:43.622205+00:00
-- url     : https://prove2.me/theorems/8ab17745-b9a2-4cc3-9b8b-59b750364e81
-- title:
--   Feasible plan of problem (PC) for a given purchase decision
-- statement:
--   Fix a planning horizon $T$, an overhead-time function $O$, a compensation function $\Pi$, a price $r$ and a time commitment $\delta$ of the discrete service, and a purchase decision $y$. A plan $(t_l,c_l,t_w,c_O)$ is **feasible** for problem (PC) when
--
--   1. $t_l,\ c_l,\ t_w,\ c_O\ \ge 0$;
--   2. (time constraint) $t_w + O(c_O) + t_l + \delta y \le T$;
--   3. (budget constraint) $c_O + c_l + r y \le \Pi(t_w)$.
--
--   Work time, overhead time, leisure time and, if the service is bought, its time commitment share the horizon $T$; earnings pay for overhead reduction, leisure consumption and, if bought, the price.
--
--   **Formalization Note** $y$ is a real number entering the constraints exactly as $\delta y$ and $r y$; the paper's $y\in\{0,1\}$ is imposed where the definition is used ($y=1$ buyer, $y=0$ non-buyer). The compensation function is arbitrary here.
-- source:
--   Li, Lariviere, Bassamboo, Is Full Price the Full Story When Consumers Have Time and Budget Constraints?, SSRN 4223388, §2.1, problem (PC), p.5

import Mathlib
import Definitions.Def_FullPriceTime_Plan

namespace FullPriceTime

/-- **Feasibility of a plan for problem (PC) with a given purchase decision.**
Li, Lariviere, Bassamboo, *Is Full Price the Full Story When Consumers Have Time and Budget
Constraints?*, SSRN 4223388, §2.1, problem (PC), p.5 (PDF p.5): the constraints
`tw + O(cO) + tl + δy ≤ T`, `cO + cl + ry ≤ Πθ(tw)`, `tl, cl, tw, cO ≥ 0`.

`IsFeasiblePlan T O comp r δ y p` holds when the plan `p = (t_l, c_l, t_w, c_O)` satisfies
1. `t_l, c_l, t_w, c_O ≥ 0`;
2. the time constraint `t_w + O(c_O) + t_l + δ·y ≤ T`;
3. the budget constraint `c_O + c_l + r·y ≤ comp(t_w)`,
where `T` is the length of the planning horizon, `O` the overhead time as a function of the
overhead expenditure, `comp` the compensation function `Π_θ`, `r` and `δ` the price and the time
commitment of the discrete service, and `y` the purchase decision.

**Formalization Note** The purchase decision `y` is a real number entering the constraints exactly
as `δ·y` and `r·y`; the paper's `y ∈ {0,1}` is imposed where the definition is used (`y = 1` for a
buyer, `y = 0` for a non-buyer). The compensation function is arbitrary here; the paper's
Proposition 1 instantiates it with `linearCompensation θ`. -/
def IsFeasiblePlan (T : ℝ) (O : ℝ → ℝ) (comp : ℝ → ℝ) (r δ y : ℝ) (p : Plan) : Prop :=
  0 ≤ p.tl ∧ 0 ≤ p.cl ∧ 0 ≤ p.tw ∧ 0 ≤ p.cO ∧
  p.tw + O p.cO + p.tl + δ * y ≤ T ∧
  p.cO + p.cl + r * y ≤ comp p.tw

end FullPriceTime


