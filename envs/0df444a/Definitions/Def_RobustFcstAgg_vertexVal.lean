-- Prove2me | Definitions.Def_RobustFcstAgg_vertexVal
-- name    : RobustFcstAgg_vertexVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:48:36.769464+00:00
-- url     : https://prove2.me/theorems/a239a1da-d816-4366-9cd5-3e5ec8d7e272
-- title:
--   Value of a vertex of a DAG on $\mathcal Q\cup\{Y\}$
-- statement:
--   An eliciting graph has vertex set $\mathcal Q\cup\{Y\}$. This assigns to each vertex its random variable under $\mathcal D$: the target $Y$, or the answer of the query.
--
--   **Formalization Note** A vertex is an element of `Option ι`, where `none` is $Y$ and `some j` is the query $Q_j$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Definition 3, p.5

import Mathlib
import Definitions.Def_RobustFcstAgg_Y
import Definitions.Def_RobustFcstAgg_Query_rv

namespace RobustFcstAgg

/-- **Value of a DAG vertex.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Definition 3, p.5: the vertices are `𝒬 ∪ {Y}`.

**Formalization Note.** A vertex is `Option ι`, with `none` the target `Y` and `some j` the query `Q j`. -/
def vertexVal {n : ℕ} {ι : Type} (Q : ι → Query n) (D : InfoStruct n) :
    Option ι → Signals n → ℝ
  | none => Y
  | some j => (Q j).rv D

end RobustFcstAgg


