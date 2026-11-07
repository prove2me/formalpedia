-- Prove2me | Definitions.Def_RobustFcstAgg_view
-- name    : RobustFcstAgg_view
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:13.626799+00:00
-- url     : https://prove2.me/theorems/75e91267-e588-443f-adfe-f2ccc5f90ba3
-- title:
--   The restriction of a realization to $S_i$
-- statement:
--   The map sending a realization $(x_T)_T$ to what expert $i$ sees, $(x_T)_{T\ni i}$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.3, p.7

import Mathlib
import Definitions.Def_RobustFcstAgg_Signals
import Definitions.Def_RobustFcstAgg_AgentSig

namespace RobustFcstAgg

/-- **What expert `i` sees.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.3, p.7: the restriction of `x` to `S_i`. -/
def view {n : ℕ} (i : Fin n) (x : Signals n) : AgentSig i → ℝ := fun T => x T.1

end RobustFcstAgg


