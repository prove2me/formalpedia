-- Prove2me | Definitions.Def_SherbrookeMetric_ConvexHull_MarginalConditions
-- name    : SherbrookeMetric_ConvexHull_MarginalConditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:03.148293+00:00
-- url     : https://prove2.me/theorems/0fb7af82-6062-4ff5-9522-87a594168673
-- title:
--   Equation (12) — marginal conditions for one item
-- statement:
--   Let $H$ be a real-valued item function on nonnegative integer stock levels, and let $c$ be its unit cost. A stock level $\bar m$ satisfies the **marginal conditions** when the next unit does not improve the objective, but the previous unit did:
--
--   $$
--   c+H(\bar m+1)-H(\bar m)\ge0,\qquad
--   \bar m>0\ \Longrightarrow\ c+H(\bar m)-H(\bar m-1)<0.
--   $$
--
--   These are Sherbrooke's conditions (12), with $H=\Xi'$ for the lower convex hull. They select the first stock level at which the marginal objective change is nonnegative.
--
--   **Formalization Note** At $\bar m=0$ the second clause is true, matching the paper's convention $\Xi'(-1)=+\infty$; natural-number subtraction is not used.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), p. 140, Appendix, Eq. (12); DOI 10.1287/opre.16.1.122

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic

namespace SherbrookeMetric.ConvexHull

/-- Equation (12), p. 140. The second line is conditional on a predecessor,
so at `m = 0` it is true, matching the paper's convention `Ξ′(-1) = ∞`. -/
def MarginalConditions (c : ℝ) (H : ℕ → ℝ) (m : ℕ) : Prop :=
  0 ≤ c + ServiceParts.StockLevels.fdiff H m ∧
    ∀ k : ℕ, m = k + 1 → c + ServiceParts.StockLevels.fdiff H k < 0

end SherbrookeMetric.ConvexHull


