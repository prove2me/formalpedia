-- Prove2me | Definitions.Def_RobustFcstAgg_Rule_output
-- name    : RobustFcstAgg_Rule_output
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:49:12.156263+00:00
-- url     : https://prove2.me/theorems/a22105e5-534a-4997-a04d-1d976cb1f95b
-- title:
--   Output $f(\mathcal Q)$ of a rule
-- statement:
--   The approximator implemented by a rule under an instance $\mathcal D$: the function $f$ applied to the answers of the queries.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Definition 1, p.4

import Mathlib
import Definitions.Def_RobustFcstAgg_Rule
import Definitions.Def_RobustFcstAgg_Query_rv

namespace RobustFcstAgg

/-- **Output of a rule under `D`:** `f(𝒬)`. Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Definition 1, p.4. -/
def Rule.output {n : ℕ} (R : Rule n) (D : InfoStruct n) (x : Signals n) : ℝ :=
  R.f fun j => (R.Q j).rv D x

end RobustFcstAgg


