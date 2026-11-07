-- Prove2me | Definitions.Def_OnlineBudgetAlloc_expD
-- name    : OnlineBudgetAlloc_expD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:42.866194+00:00
-- url     : https://prove2.me/theorems/7fb80568-e158-4b6e-8d51-8abdf973c159
-- title:
--   Expectation over the input distribution $D_{N,d}$
-- statement:
--   For a real function $f$ of the seed, its **expectation** under $D_{N,d}$ is the average over all seeds,
--   $$
--   \mathbb E_{D_{N,d}}[f] = \frac{1}{|\mathrm{Seed}|} \sum_{\text{seed}} f(\text{seed}).
--   $$
--   "Throughout the proof, unless conditioned otherwise, expectations are over the input distribution $D_{N,d}$" (p.4).
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.2, p.4

import Mathlib
import Definitions.Def_OnlineBudgetAlloc_Seed

namespace OnlineBudgetAlloc

/-- The expectation `E[f]` of a function of the seed under `D_{N,d}` (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.2, p.4:
"expectations are over the input distribution DN,d"): the average of `f` over all seeds. -/
noncomputable def expD {N d : ℕ} (f : Seed N d → ℝ) : ℝ :=
  (∑ s, f s) / (Fintype.card (Seed N d) : ℝ)

end OnlineBudgetAlloc


