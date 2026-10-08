-- Prove2me | Definitions.Def_SherbrookeMetric_ConvexHull_DiscreteConvex
-- name    : SherbrookeMetric_ConvexHull_DiscreteConvex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:53.663506+00:00
-- url     : https://prove2.me/theorems/68d47dbe-c3e0-4931-bc69-cc26472c90ed
-- title:
--   Appendix — discrete convexity of a stock-level function
-- statement:
--   A real-valued function $g$ on the nonnegative integers is **discretely convex** when its forward marginal changes do not decrease. With $\Delta g(m)=g(m+1)-g(m)$ and $\Delta^2g(m)=\Delta g(m+1)-\Delta g(m)$, this means
--
--   $$
--   \Delta^2g(m)\ge 0\qquad\text{for every }m\ge 0.
--   $$
--
--   This is the convexity property used for the lower boundary of the item cost function in the Appendix. The forward differences are the previously published stock-level definitions.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), p. 140, Appendix; DOI 10.1287/opre.16.1.122

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic

namespace SherbrookeMetric.ConvexHull

/-- Appendix, p. 140: convexity of a real sequence on stock levels `0, 1, 2, …`
means that its successive forward differences do not decrease. -/
def DiscreteConvex (g : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 0 ≤ ServiceParts.StockLevels.fdiff2 g m

end SherbrookeMetric.ConvexHull


