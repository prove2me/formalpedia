-- Prove2me | Definitions.Def_RobustFcstAgg_gridSet
-- name    : RobustFcstAgg_gridSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:41:22.304634+00:00
-- url     : https://prove2.me/theorems/cfcc70c9-4d1f-4a8f-ba5e-30dbe6269043
-- title:
--   Upper values of $\max_{t\in[n]}p(t)^2$ over $P_d$, $p(0)=1$
-- statement:
--   The set of $E$ such that some polynomial $p$ of degree at most $d$ with $p(0)=1$ has $p(t)^2\le E$ for every $t\in\{1,\dots,n\}$. Its least element is
--   $$\min_{p\in P_d,\ p(0)=1}\ \max_{t\in[n]}p(t)^2,$$
--   the right side of (4).
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Lemma 6, p.16

import Mathlib
open Polynomial

namespace RobustFcstAgg

/-- **Upper values of the grid problem with squares.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Lemma 6, p.16: the set of `E` with `p(t)² ≤ E` on `[n]` for some
`p ∈ P_d`, `p(0) = 1`. Its least element is `min_{p ∈ P_d, p(0) = 1} max_{t ∈ [n]} p(t)²`.

**Formalization Note.** `P_d` (p.12) has degree *at most* `d`. At `n = 0` the set is all of `ℝ` and has no least element. -/
def gridSet (n d : ℕ) : Set ℝ :=
  {E | ∃ p : ℝ[X], p.natDegree ≤ d ∧ p.eval 0 = 1 ∧ ∀ t ∈ Finset.Icc 1 n, (p.eval (t : ℝ)) ^ 2 ≤ E}

end RobustFcstAgg


