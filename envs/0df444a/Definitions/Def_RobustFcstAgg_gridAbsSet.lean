-- Prove2me | Definitions.Def_RobustFcstAgg_gridAbsSet
-- name    : RobustFcstAgg_gridAbsSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:41:22.627879+00:00
-- url     : https://prove2.me/theorems/213f8b52-63cf-49f7-8ef2-88bf6653e177
-- title:
--   Upper values of $\max_{t\in[n]}|p(t)|$ over $P_d$, $p(0)=1$
-- statement:
--   The set of $E$ such that some polynomial $p$ of degree at most $d$ with $p(0)=1$ has $|p(t)|\le E$ for every $t\in\{1,\dots,n\}$. Its least element is
--   $$\min_{p\in P_d,\ p(0)=1}\ \max_{t\in\{1,\dots,n\}}|p(t)|.$$
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Lemma 11, p.29

import Mathlib
open Polynomial

namespace RobustFcstAgg

/-- **Upper values of the grid problem.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Lemma 11, p.29: the set of `E` with `|p(t)| ≤ E` on `{1,…,n}` for some
`p ∈ P_d`, `p(0) = 1`. Its least element is `min_{p ∈ P_d, p(0) = 1} max_{t ∈ {1,…,n}} |p(t)|`. -/
def gridAbsSet (n d : ℕ) : Set ℝ :=
  {E | ∃ p : ℝ[X], p.natDegree ≤ d ∧ p.eval 0 = 1 ∧ ∀ t ∈ Finset.Icc 1 n, |p.eval (t : ℝ)| ≤ E}

end RobustFcstAgg


