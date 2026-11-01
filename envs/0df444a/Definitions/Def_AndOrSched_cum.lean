-- Prove2me | Definitions.Def_AndOrSched_cum
-- name    : AndOrSched_cum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:09.923405+00:00
-- url     : https://prove2.me/theorems/f66ddab8-e553-4ac6-bbd2-ff782f5cbf83
-- title:
--   Cumulative LP mass $\sum_{s\le t}x_{js}$
-- statement:
--   For an LP solution $x$, the cumulative sum $\sum_{s=1}^{t}x_{js}$: the fraction of job $j$ completed by time slot $t$ (LP (1)) or by the end of interval $t$ (LP (5)).
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.7, p.9

import Mathlib
open scoped Classical NNReal

namespace AndOrSched

/-- The cumulative LP value `Σ_{s=1}^{t} x_{js}`: the fraction of job `j` completed by time slot
`t` in LP (1), or by the end of interval `t` in LP (5) (Happach, Schulz, arXiv:2001.07011v1, §2, p.7 and p.9). -/
def cum {J : Type} (x : J → ℕ → ℝ) (j : J) (t : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 t, x j s

end AndOrSched


