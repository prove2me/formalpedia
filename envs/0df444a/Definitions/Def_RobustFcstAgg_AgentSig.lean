-- Prove2me | Definitions.Def_RobustFcstAgg_AgentSig
-- name    : RobustFcstAgg_AgentSig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:16.608168+00:00
-- url     : https://prove2.me/theorems/8fa505a2-a902-421e-9d30-b2ad5e144ca7
-- title:
--   Coordinates of expert $i$: $\{T: i\in T\}$
-- statement:
--   Expert $i$ observes the signal $S_i=\{X_T: i\in T\}$. This type indexes its coordinates: the nonempty $T$ containing $i$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.3, p.7

import Mathlib
import Definitions.Def_RobustFcstAgg_Subs

namespace RobustFcstAgg

/-- **Coordinates of expert `i`'s signal.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.3, p.7: "`S_i = {X_T : i ∈ T}`". -/
abbrev AgentSig {n : ℕ} (i : Fin n) : Type := {T : Subs n // i ∈ T.1}

end RobustFcstAgg


