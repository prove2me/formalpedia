-- Prove2me | Definitions.Def_RobustFcstAgg_Rest
-- name    : RobustFcstAgg_Rest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:08.52755+00:00
-- url     : https://prove2.me/theorems/19d14710-23a6-44ff-8b77-5db4249a38e1
-- title:
--   Coordinates hidden from expert $i$: $\{T: i\notin T\}$
-- statement:
--   The nonempty sets $T$ not containing $i$ index the signals hidden from expert $i$. They are independent of $S_i$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.3, p.7

import Mathlib
import Definitions.Def_RobustFcstAgg_Subs

namespace RobustFcstAgg

/-- **Coordinates hidden from expert `i`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.3, p.7: the signals `X_T` with `i ∉ T`, which
are independent of `S_i`. -/
abbrev Rest {n : ℕ} (i : Fin n) : Type := {T : Subs n // i ∉ T.1}

end RobustFcstAgg


