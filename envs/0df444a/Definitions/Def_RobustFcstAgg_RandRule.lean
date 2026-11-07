-- Prove2me | Definitions.Def_RobustFcstAgg_RandRule
-- name    : RobustFcstAgg_RandRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:01.914005+00:00
-- url     : https://prove2.me/theorems/d766f78c-54a8-4729-adb4-f32f42d32494
-- title:
--   Randomized aggregation rule (Definition 1)
-- statement:
--   A **randomized aggregation rule** is a distribution $P$ on a sample space: a random context $Z\sim P$ is drawn first, and determines the aggregation rule $(\mathcal Q_Z,f_Z)$.
--
--   **Formalization Note** The context is drawn independently of the signals and neither its law nor the map to rules depends on $\mathcal D$. The sample space lives in `Type`.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Definition 1, p.4

import Mathlib
import Definitions.Def_RobustFcstAgg_Rule
open MeasureTheory

namespace RobustFcstAgg

/-- **Randomized aggregation rule.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Definition 1, p.4: "a random context `Z ∼ P` is drawn first from some
sample space `Ω`, determining the resulting aggregation rule `(Q_Z, f_Z)`".

**Formalization Note.** `Z` is drawn independently of the signals, and neither `P` nor `rule` depends on `D`. Each
realization may have its own index type. Regularity lives in `RandRule.IsOrderAgentLE`, so that a deterministic
`Rule` is a `RandRule` without proof obligations (`Rule.toRand`). -/
structure RandRule (n : ℕ) where
  /-- The sample space of the context. -/
  Z : Type
  [mZ : MeasurableSpace Z]
  /-- The distribution of the context. -/
  P : Measure Z
  [prob : IsProbabilityMeasure P]
  /-- The rule determined by the context. -/
  rule : Z → Rule n

attribute [instance] RandRule.mZ RandRule.prob

end RobustFcstAgg


