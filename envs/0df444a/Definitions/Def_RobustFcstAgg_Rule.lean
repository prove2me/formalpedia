-- Prove2me | Definitions.Def_RobustFcstAgg_Rule
-- name    : RobustFcstAgg_Rule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:47:01.813093+00:00
-- url     : https://prove2.me/theorems/c2ca117c-862d-4ea8-9bf7-83af40ad60e0
-- title:
--   Deterministic aggregation rule $R=(\mathcal Q,f)$ (Definition 1)
-- statement:
--   A **deterministic aggregation rule** $R=(\mathcal Q,f)$ is a finite indexed collection of queries $\mathcal Q$ with a Borel-measurable function $f:\mathbb R^{\mathcal Q}\to\mathbb R$ from query outputs to a real number.
--
--   The function $f$ takes no argument for $\mathcal D$: the principal does not know the instance.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Definition 1, p.4

import Mathlib
import Definitions.Def_RobustFcstAgg_Query

namespace RobustFcstAgg

/-- **Deterministic aggregation rule `R = (𝒬, f)`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Definition 1, p.4: a finite indexed collection of
queries and a Borel-measurable `f : ℝ^𝒬 → ℝ`.

**Formalization Note.** `f` takes no `D` argument: the principal does not know `D` (p.4). -/
structure Rule (n : ℕ) where
  /-- The index type of the collection. -/
  ι : Type
  [fin : Fintype ι]
  /-- The queries. -/
  Q : ι → Query n
  /-- The aggregation function. -/
  f : (ι → ℝ) → ℝ
  measurable_f : Measurable f

attribute [instance] Rule.fin

end RobustFcstAgg


