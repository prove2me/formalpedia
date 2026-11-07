-- Prove2me | Definitions.Def_RobustFcstAgg_Subs
-- name    : RobustFcstAgg_Subs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:41:00.836956+00:00
-- url     : https://prove2.me/theorems/ffca9c64-0c26-4530-bc3e-1318e4dd891b
-- title:
--   Index set of the signals: nonempty subsets of $[n]$
-- statement:
--   The **index set of the signals** is the family of nonempty subsets $T\subseteq[n]$. In the partial information model there is one signal $X_T$ for each subset $T$, revealed exactly to the experts in $T$.
--
--   **Formalization Note** $[n]$ is `Fin n`. The empty subset is not indexed: the source sets $X_\emptyset=0$ with probability one, so it contributes nothing to any sum.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.3, p.7

import Mathlib

namespace RobustFcstAgg

/-- **Index set of the signals.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.3, p.7: one signal `X_T` for each `T ⊆ [n]`.

**Formalization Note.** `[n]` is `Fin n`. Only nonempty `T` are indexed: the source sets `X_∅ = 0` with
probability one "for mathematical convenience", so `X_∅` contributes nothing to any sum. -/
abbrev Subs (n : ℕ) : Type := {T : Finset (Fin n) // T.Nonempty}

end RobustFcstAgg


