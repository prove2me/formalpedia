-- Prove2me | Definitions.Def_LowRankMEG_epsSchedule
-- name    : LowRankMEG_epsSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:20.859857+00:00
-- url     : https://prove2.me/theorems/73b12ae9-b419-46ca-8cac-613dafbb36c6
-- title:
--   The schedule $\varepsilon_t$ of Theorem 5
-- statement:
--   For $t\ge0$,
--   $$
--   \varepsilon_t=\frac{3\tilde\varepsilon_0}{2\max\{G^2,1\}}\cdot\frac1{(t+c+1)^3}.
--   $$
--   Its summability keeps the iterates in the warm-start ball.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Theorem 5, p.23

import Mathlib

namespace LowRankMEG

/-- **The schedule of Theorem 5**, `ε_t = (3ε̃₀/(2 max{G², 1})) · 1/(t + c + 1)³`, for `t ≥ 0`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Theorem 5, p.23.

**Formalization Note.** `c` is real, as on the page. -/
noncomputable def epsSchedule (G εt c : ℝ) (t : ℕ) : ℝ :=
  3 * εt / (2 * max (G ^ 2) 1) * (1 / ((t : ℝ) + c + 1) ^ 3)

end LowRankMEG


