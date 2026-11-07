-- Prove2me | Definitions.Def_RobustFcstAgg_Rule_toRand
-- name    : RobustFcstAgg_Rule_toRand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:51:30.275354+00:00
-- url     : https://prove2.me/theorems/016dfbfc-2bc3-4366-9cbc-4bcabe270a35
-- title:
--   A deterministic rule as a randomized one
-- statement:
--   A deterministic rule $R$ is the randomized rule whose context has a point-mass law and which always produces $R$. The loss and the error of a deterministic rule are those of this randomized rule.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Definition 1, p.4

import Mathlib
import Definitions.Def_RobustFcstAgg_RandRule
open MeasureTheory

namespace RobustFcstAgg

/-- **A deterministic rule as a randomized one.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Definition 1, p.4: the point mass on `R`. -/
noncomputable def Rule.toRand {n : ℕ} (R : Rule n) : RandRule n where
  Z := Unit
  P := Measure.dirac ()
  rule := fun _ => R

end RobustFcstAgg


