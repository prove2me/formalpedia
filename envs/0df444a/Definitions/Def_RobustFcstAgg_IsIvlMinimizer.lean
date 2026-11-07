-- Prove2me | Definitions.Def_RobustFcstAgg_IsIvlMinimizer
-- name    : RobustFcstAgg_IsIvlMinimizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:26.185113+00:00
-- url     : https://prove2.me/theorems/9e6e580b-8304-4065-852f-6fa23facac4a
-- title:
--   Minimizer of $\max_{x\in[1,n]}|p(x)|$ over $P_d$, $p(0)=1$
-- statement:
--   A polynomial $p$ is a **minimizer** if it has degree at most $d$, satisfies $p(0)=1$, and its supremum on $[1,n]$ equals the minimum value of the interval problem:
--   $$p\in\arg\min_{p\in P_d,\ p(0)=1}\ \max_{x\in[1,n]}|p(x)|.$$
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Lemma 9, p.27

import Mathlib
import Definitions.Def_RobustFcstAgg_ivlSet
open Polynomial

namespace RobustFcstAgg

/-- **Minimizer of the interval problem.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Lemma 9, p.27:
"`p* ∈ arg min_{p ∈ P_d, p(0) = 1} max_{t ∈ [1,n]} |p(t)|`". The polynomial is admissible and its sup norm on `[1, n]` is
at most the minimum value. -/
def IsIvlMinimizer (n d : ℕ) (p : ℝ[X]) : Prop :=
  p.natDegree ≤ d ∧ p.eval 0 = 1 ∧
    ∃ E, IsLeast (ivlSet n d) E ∧ ∀ x ∈ Set.Icc (1 : ℝ) n, |p.eval x| ≤ E

end RobustFcstAgg


