-- Prove2me | Definitions.Def_CachonCoord_DemandUpdate_Profits
-- name    : CachonCoord_DemandUpdate_Profits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:45:33.088605+00:00
-- url     : https://prove2.me/theorems/3ad00595-0995-4781-99ad-7dbec852cb9a
-- title:
--   §6.6.1, pp. 65–66 — the firms' profits under the buy back contract {w₁, w₂, b}: π₂, π₁, Π₂ and Π₁
-- statement:
--   These are the firms' profits in the newsvendor with demand updating under the buy back contract $\{w_1, w_2, b\}$. The retailer pays $w_i$ per unit ordered in period $i$, and the supplier buys back every unsold unit at $b$.
--
--   1. The retailer's period-2 expected revenue minus period-2 procurement cost, when the supplier delivers in full (p. 65), is
--   $$\pi_2(q_2\,|\,q_1,\xi) = (p-b)S(q_2\,|\,\xi) - (w_2-b)q_2 + w_2 q_1 .$$
--   2. The retailer's period-1 expected profit, when in period 2 he orders a supply chain optimal $q_2(q_1,\xi)$, is
--   $$\pi_1(q_1) = -w_1 q_1 + E\big[\pi_2(q_2(q_1,\xi)\,|\,q_1,\xi)\big].$$
--   3. Let the supply chain hold $x \ge q_1$ units at the start of period 2, and let the retailer hold $y$ units after the supplier's period-2 delivery, $x \le y \le q_2$. The supplier's period-2 profit (p. 65) is
--   $$\Pi_2(y\,|\,x,q_1,q_2,\xi) = bS(y\,|\,\xi) - by + w_2(y-q_1) - (y-x)c_2 .$$
--   4. If the supplier fills the order $q_2$ entirely, producing $(q_2 - x)^+$ units in period 2, her period-2 profit is
--   $$\Pi_2(x,q_1,q_2,\xi) = bS(q_2\,|\,\xi) - bq_2 + w_2(q_2-q_1) - (q_2-x)^+c_2 .$$
--   5. Her period-1 expected profit as a function of period-1 production $x$ (p. 66) is
--   $$\Pi_1(x\,|\,q_1) = -c_1 x + E\big[\Pi_2(x,q_1,q_2(q_1,\xi),\xi)\big].$$
--
--   The coordination results of §6.6.1 are statements about these functions.
--
--   **Formalization Note** The printed first line of $\Pi_2(x,q_1,q_2,\xi)$ on p. 66 omits $w_2(q_2-q_1)$. The term is included here because $\Pi_2(x,\cdot)$ is the p. 65 profit at $y = q_2$; it does not depend on $x$, so no claim about $x$ changes. As on the page, $\pi_1$ and $\Pi_1$ use the supply chain optimal period-2 order (the retailer orders it, and the supplier fills it, by the results on p. 65). The supplier's period-1 revenue $w_1 q_1$ does not depend on $x$ and is left out of $\Pi_1$, as on p. 66.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.6.1, pp. 65–66 (displays of π₂, Π₂(y|x, q₁, q₂, ξ), π₁, Π₂(x, q₁, q₂, ξ), Π₁(x|q₁))

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

namespace Model

variable (M : Model)

/-- p. 65: the retailer's period-2 expected revenue minus period-2 procurement cost under the
buy back contract `{w_1, w_2, b}`, when the supplier delivers in full,
`π_2(q_2|q_1, ξ) = (p − b)S(q_2|ξ) − (w_2 − b)q_2 + w_2 q_1`. -/
noncomputable def retailerProfit2 (w2 b q1 ξ q2 : ℝ) : ℝ :=
  (M.p - b) * M.S ξ q2 - (w2 - b) * q2 + w2 * q1

/-- The retailer's period-1 expected profit `π_1(q_1) = −w_1 q_1 + E[π_2(q_2(q_1, ξ)|q_1, ξ)]`:
he pays `w_1` per unit ordered in period 1 and orders the supply chain optimal `q_2(q_1, ξ)`
(selection `q2sel`) in period 2 (p. 66). -/
noncomputable def retailerProfit1 (w1 w2 b : ℝ) (q2sel : ℝ → ℝ → ℝ) (q1 : ℝ) : ℝ :=
  -w1 * q1 + M.E (fun ξ => M.retailerProfit2 w2 b q1 ξ (q2sel q1 ξ))

/-- p. 65: the supplier's period-2 profit when the supply chain holds `x ≥ q_1` units at the
start of period 2 and the retailer holds `y` units after the supplier's delivery,
`Π_2(y|x, q_1, q_2, ξ) = bS(y|ξ) − by + w_2(y − q_1) − (y − x)c_2` (for `x ≤ y ≤ q_2`). -/
noncomputable def supplierProfit2Fill (w2 b x q1 ξ y : ℝ) : ℝ :=
  b * M.S ξ y - b * y + w2 * (y - q1) - (y - x) * M.c2

/-- p. 66: the supplier's period-2 profit when she fills the retailer's order `q_2` entirely,
`bS(q_2|ξ) − bq_2 + w_2(q_2 − q_1) − (q_2 − x)⁺c_2`, i.e. the p. 65 profit at `y = q_2` with
production `(q_2 − x)⁺`. (The printed first line on p. 66 omits the term `w_2(q_2 − q_1)`,
which does not depend on `x`.) -/
noncomputable def supplierProfit2 (w2 b x q1 q2 ξ : ℝ) : ℝ :=
  b * M.S ξ q2 - b * q2 + w2 * (q2 - q1) - max (q2 - x) 0 * M.c2

/-- p. 66: the supplier's period-1 expected profit as a function of her period-1 production `x`,
`Π_1(x|q_1) = −c_1 x + E[Π_2(x, q_1, q_2, ξ)]` with `q_2 = q_2(q_1, ξ)` (selection `q2sel`). -/
noncomputable def supplierProfit1 (w2 b : ℝ) (q2sel : ℝ → ℝ → ℝ) (q1 x : ℝ) : ℝ :=
  -M.c1 * x + M.E (fun ξ => M.supplierProfit2 w2 b x q1 (q2sel q1 ξ) ξ)

end Model

end CachonCoord.DemandUpdate


