-- Prove2me | Definitions.Def_FreeSpencer_bound
-- name    : FreeSpencer_bound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:57.166626+00:00
-- url     : https://prove2.me/theorems/7b6db43f-3a35-402f-bd3f-c0346f5bbcbb
-- title:
--   The discrepancy bound $4000\sqrt{n\max\{1,1+\log(2m/n)\}}$
-- statement:
--   The bound of Theorem 1.1,
--   $$\mathrm{bound}(n,m)=4000\sqrt{n\max\{1,\,1+\log(2m/n)\}},$$
--   with the natural logarithm. For $2m<n$ the logarithm is negative and the maximum is $1$.
--
--   **Formalization Note** At $n=0$ or $m=0$ Lean's conventions $x/0=0$, $\log 0=0$ give the values $0$ and $4000\sqrt n$; the signed sum is then the zero matrix.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem 1.1, p.2

import Mathlib

namespace FreeSpencer

/-- The bound of Theorem 1.1: `4000 √(n · max{1, 1 + log(2m/n)})` with the natural logarithm.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem 1.1, p.2 (natural log: p.64).

**Formalization Note** At `n = 0` Lean's `x / 0 = 0` and `log 0 = 0` give `bound 0 m = 0`; at `m = 0`
it gives `4000 √n`. In both cases the signed sum is the zero matrix (empty sum or `0 × 0`), so
nothing is lost. For `2m < n` the logarithm is negative and the maximum is `1`. -/
noncomputable def bound (n m : ℕ) : ℝ :=
  4000 * Real.sqrt ((n : ℝ) * max 1 (1 + Real.log (2 * (m : ℝ) / (n : ℝ))))

end FreeSpencer


