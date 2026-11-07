-- Prove2me | Definitions.Def_OnlineBudgetAlloc_vcap
-- name    : OnlineBudgetAlloc_vcap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:41.273006+00:00
-- url     : https://prove2.me/theorems/2dc68be4-a54c-419b-93d8-79d23cb4fbaa
-- title:
--   Capped remaining budget $v(r) = \max(r - 1/12, 0)$
-- statement:
--   The **capped remaining budget** of an advertiser with remaining budget $r$ is
--   $$
--   v(r) = \max\Bigl(r - \frac{1}{12}, 0\Bigr).
--   $$
--   It enters the potential $\varphi(t) = \mathrm{ALG}_t + H\cdot \bar v_t$, where $\bar v_t$ is the average of $v$ over the remaining advertisers. Capping every budget at $11/12$ is what lets the middle phase beat the classical $1 - 1/e$ bound.
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.2, p.4

import Mathlib

namespace OnlineBudgetAlloc

/-- The **capped remaining budget** `v(r) = max(r − 1/12, 0)` (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.2, p.4). -/
noncomputable def vcap (r : ℝ) : ℝ := max (r - 1 / 12) 0

end OnlineBudgetAlloc


