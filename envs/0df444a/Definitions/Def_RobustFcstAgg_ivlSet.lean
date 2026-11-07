-- Prove2me | Definitions.Def_RobustFcstAgg_ivlSet
-- name    : RobustFcstAgg_ivlSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:41:32.511148+00:00
-- url     : https://prove2.me/theorems/bd824c2f-8be6-40f9-8dc3-f27a123dd64d
-- title:
--   Upper values of $\max_{x\in[1,n]}|p(x)|$ over $P_d$, $p(0)=1$
-- statement:
--   The set of $E$ such that some polynomial $p$ of degree at most $d$ with $p(0)=1$ has $|p(x)|\le E$ for every real $x\in[1,n]$. Its least element is
--   $$\min_{p\in P_d,\ p(0)=1}\ \max_{x\in[1,n]}|p(x)|.$$
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Lemma 9, p.27

import Mathlib
open Polynomial

namespace RobustFcstAgg

/-- **Upper values of the interval problem.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Lemma 9, p.27: the set of `E` with `|p(x)| ≤ E` on `[1, n]` for some
`p ∈ P_d`, `p(0) = 1`. Its least element is `min_{p ∈ P_d, p(0) = 1} max_{x ∈ [1, n]} |p(x)|`. -/
def ivlSet (n d : ℕ) : Set ℝ :=
  {E | ∃ p : ℝ[X], p.natDegree ≤ d ∧ p.eval 0 = 1 ∧ ∀ x ∈ Set.Icc (1 : ℝ) n, |p.eval x| ≤ E}

end RobustFcstAgg


