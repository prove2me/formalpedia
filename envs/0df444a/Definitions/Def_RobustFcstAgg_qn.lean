-- Prove2me | Definitions.Def_RobustFcstAgg_qn
-- name    : RobustFcstAgg_qn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:27.60929+00:00
-- url     : https://prove2.me/theorems/ee19497d-2011-4c7b-9390-d26d78d02c44
-- title:
--   $q(n)=(\sqrt n+1)/(\sqrt n-1)$
-- statement:
--   The base of the extremal value:
--   $$q(n)=\frac{\sqrt n+1}{\sqrt n-1}.$$
--
--   **Formalization Note** Undefined in the source at $n=1$. Every statement using it assumes $n\ge2$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Inequality (6), p.17; Lemma 10, p.29

import Mathlib

namespace RobustFcstAgg

/-- **`q(n) = (√n + 1)/(√n − 1)`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Inequality (6), p.17, and Lemma 10, p.29.

**Formalization Note.** Real arithmetic. For `n = 1` the source's formula is undefined (Lean's value is `0`); every
statement using `qn` assumes `2 ≤ n`. -/
noncomputable def qn (n : ℕ) : ℝ := (√(n : ℝ) + 1) / (√(n : ℝ) - 1)

end RobustFcstAgg


