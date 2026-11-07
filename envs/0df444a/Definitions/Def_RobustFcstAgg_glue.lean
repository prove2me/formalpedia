-- Prove2me | Definitions.Def_RobustFcstAgg_glue
-- name    : RobustFcstAgg_glue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:00.528875+00:00
-- url     : https://prove2.me/theorems/7cec443a-1313-438c-9cd6-6fd5b44f55af
-- title:
--   Assembling a realization from $S_i$ and the hidden signals
-- statement:
--   Given values $s$ of the signals seen by expert $i$ and values $y$ of the hidden ones, this is the realization that equals $s$ on $\{T:i\in T\}$ and $y$ on $\{T:i\notin T\}$. It is used to write conditioning on $S_i$ as an integral over the hidden signals.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.3, p.7; Condition 1, p.25

import Mathlib
import Definitions.Def_RobustFcstAgg_Signals
import Definitions.Def_RobustFcstAgg_AgentSig
import Definitions.Def_RobustFcstAgg_Rest

namespace RobustFcstAgg

/-- **Assembling a realization from `S_i` and the rest.** The realization equal to `s` on `{T : i ∈ T}`
and to `y` on `{T : i ∉ T}`. Used to write conditioning on `S_i` as a fibre integral. -/
def glue {n : ℕ} (i : Fin n) (s : AgentSig i → ℝ) (y : Rest i → ℝ) : Signals n :=
  fun T => if h : i ∈ T.1 then s ⟨T, h⟩ else y ⟨T, h⟩

end RobustFcstAgg


