-- Prove2me | Definitions.Def_RobustFcstAgg_OrderLE
-- name    : RobustFcstAgg_OrderLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:28.513038+00:00
-- url     : https://prove2.me/theorems/76faabf8-ab73-4bff-b2c6-b18f87a72844
-- title:
--   Order at most $d$ on a DAG: $\max_Q\ell_G(Q)\le d$
-- statement:
--   $\ell_G(Q)$ is the longest path distance from $Q$ to $Y$ in $G$. This predicate says that $\max_{Q}\ell_G(Q)\le d$.
--
--   **Formalization Note** Written as: every walk from a query has at most $d$ edges. On a DAG that elicits $\mathcal Q$ every walk extends to $Y$, so this is the longest-path bound.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.2, p.6

import Mathlib
import Definitions.Def_RobustFcstAgg_HasWalk

namespace RobustFcstAgg

/-- **Order at most `d` on a DAG: `max_Q ℓ_G(Q) ≤ d`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.2, p.6: "`ℓ_G(Q)` denotes the longest path
distance from query `Q` to `Y`".

**Formalization Note.** Every walk from a query has at most `d` edges. On a DAG eliciting `𝒬` every walk extends to
`Y`, so the longest walk from `Q` is the longest path to `Y`. No `sSup` of a possibly unbounded set of naturals. -/
def OrderLE {ι : Type} (out : ι → Finset (Option ι)) (d : ℕ) : Prop :=
  ∀ j k, HasWalk out (some j) k → k ≤ d

end RobustFcstAgg


