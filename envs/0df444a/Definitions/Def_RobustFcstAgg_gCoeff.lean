-- Prove2me | Definitions.Def_RobustFcstAgg_gCoeff
-- name    : RobustFcstAgg_gCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:27.746197+00:00
-- url     : https://prove2.me/theorems/15be539d-4b4a-4c45-9f08-8c52744854c3
-- title:
--   Residual coefficient $g_T(\beta)$
-- statement:
--   For coefficients $\beta$ and a nonempty set $T$,
--   $$g_T(\beta)=1-\sum_{S:\,1\le|S|\le d,\ S\subseteq T}\beta_S,$$
--   the coefficient of $X_T$ in $Y-\sum_S\beta_S\,\mathrm{inter}(S)$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Eq. (3), p.15

import Mathlib
import Definitions.Def_RobustFcstAgg_Subs
import Definitions.Def_RobustFcstAgg_InterIndex

namespace RobustFcstAgg

/-- **Residual coefficient.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Eq. (3), p.15: "`g_T(β) := 1 − Σ_{S : 1 ≤ |S| ≤ d, S ⊆ T} β_S`". -/
def gCoeff {n d : ℕ} (β : InterIndex n d → ℝ) (T : Subs n) : ℝ :=
  1 - ∑ S : InterIndex n d with S.1 ⊆ T.1, β S

end RobustFcstAgg


