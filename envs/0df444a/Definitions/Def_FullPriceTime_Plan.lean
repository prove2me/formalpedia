-- Prove2me | Definitions.Def_FullPriceTime_Plan
-- name    : FullPriceTime_Plan
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:05.847826+00:00
-- url     : https://prove2.me/theorems/d7f1ff6f-3c57-4b56-bd7c-be4abe5125eb
-- title:
--   Plan $(t_l, c_l, t_w, c_O)$ of the consumer's problem (PC)
-- statement:
--   A **plan** of the consumer's time-and-money allocation problem (PC) is a quadruple of real numbers
--   $$p = (t_l,\ c_l,\ t_w,\ c_O),$$
--   where $t_l$ is the time spent on the continuous leisure activity, $c_l$ the money spent on it, $t_w$ the time spent working and $c_O$ the money spent on reducing overhead activities (laundry, commuting, chores).
--
--   The binary purchase decision $y\in\{0,1\}$ for the discrete service is not part of a plan; it is fixed separately (buyer $y=1$, non-buyer $y=0$).
--
--   **Formalization Note** The four fields are arbitrary reals; the sign constraints $t_l,c_l,t_w,c_O\ge 0$ of (PC) are imposed by the feasibility predicate.
-- source:
--   Li, Lariviere, Bassamboo, Is Full Price the Full Story When Consumers Have Time and Budget Constraints?, SSRN 4223388, §2.1, problem (PC), p.5

import Mathlib

namespace FullPriceTime

/-- **A plan of the consumer's problem (PC): leisure time, leisure consumption, work time and
overhead expenditure.**
Li, Lariviere, Bassamboo, *Is Full Price the Full Story When Consumers Have Time and Budget
Constraints?*, SSRN 4223388, §2.1, problem (PC), p.5 (PDF p.5).

A plan records the four continuous decision variables of (PC): the leisure time `tl` (`t_l`), the
leisure consumption `cl` (`c_l`), the work time `tw` (`t_w`) and the overhead expenditure `cO`
(`c_O`). The purchase decision `y ∈ {0,1}` is not part of a plan: it is fixed separately (buyer
`y = 1`, non-buyer `y = 0`).

**Formalization Note** The fields are arbitrary reals; non-negativity is one of the constraints of
(PC) and is imposed by `IsFeasiblePlan`. -/
structure Plan where
  /-- Leisure time `t_l`. -/
  tl : ℝ
  /-- Leisure consumption `c_l`. -/
  cl : ℝ
  /-- Work time `t_w`. -/
  tw : ℝ
  /-- Overhead expenditure `c_O`. -/
  cO : ℝ

end FullPriceTime


