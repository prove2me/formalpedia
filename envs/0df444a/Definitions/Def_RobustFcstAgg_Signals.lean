-- Prove2me | Definitions.Def_RobustFcstAgg_Signals
-- name    : RobustFcstAgg_Signals
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:42:54.783395+00:00
-- url     : https://prove2.me/theorems/28b42baf-6500-41b2-9334-bfc6711fb167
-- title:
--   Signal realizations $(X_T)_T$
-- statement:
--   A **signal realization** is a family of reals $x=(x_T)_{\emptyset\ne T\subseteq[n]}$, one value for each signal, on the product $\sigma$-algebra.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.3, p.7

import Mathlib
import Definitions.Def_RobustFcstAgg_Subs

namespace RobustFcstAgg

/-- **Signal realizations.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.3, p.7: a realization `(X_T)_T` of all the signals,
with the product σ-algebra (inferred from `Pi`). -/
abbrev Signals (n : ℕ) : Type := Subs n → ℝ

end RobustFcstAgg


