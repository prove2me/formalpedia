-- Prove2me | Definitions.Def_RobustFcstAgg_Y
-- name    : RobustFcstAgg_Y
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:44:39.089801+00:00
-- url     : https://prove2.me/theorems/503ee7fe-9291-499e-ae28-dd13dc8748a0
-- title:
--   The target $Y=\sum_T X_T$
-- statement:
--   The aggregator aims to estimate the sum of all signals,
--   $$Y=\sum_{T\subseteq[n]}X_T.$$
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.3, p.7

import Mathlib
import Definitions.Def_RobustFcstAgg_Signals

namespace RobustFcstAgg

/-- **The target `Y = Σ_T X_T`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.3, p.7. -/
def Y {n : ℕ} (x : Signals n) : ℝ := ∑ T, x T

end RobustFcstAgg


