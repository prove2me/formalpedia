-- Prove2me | Definitions.Def_RobustFcstAgg_Query_rv
-- name    : RobustFcstAgg_Query_rv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:46:46.404278+00:00
-- url     : https://prove2.me/theorems/bbdb49c9-b0fc-4de0-bc08-90149a56e9b9
-- title:
--   The answer to a query as a random variable
-- statement:
--   The source overloads $Q=Q(S_i,\mathcal D)$ to mean also the random variable output by the query: the answer computed on the part of the realization that expert $i$ sees.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.1, p.4

import Mathlib
import Definitions.Def_RobustFcstAgg_Signals
import Definitions.Def_RobustFcstAgg_view
import Definitions.Def_RobustFcstAgg_Query

namespace RobustFcstAgg

/-- **The query's answer as a random variable.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.1, p.4: "we overload notation and let
`Q = Q(S_i, D)` also denote the random variable output of a query". -/
def Query.rv {n : ℕ} (q : Query n) (D : InfoStruct n) (x : Signals n) : ℝ :=
  q.eval D (view q.agent x)

end RobustFcstAgg


