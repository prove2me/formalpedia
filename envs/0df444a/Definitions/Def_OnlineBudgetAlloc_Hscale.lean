-- Prove2me | Definitions.Def_OnlineBudgetAlloc_Hscale
-- name    : OnlineBudgetAlloc_Hscale
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:37.394798+00:00
-- url     : https://prove2.me/theorems/a7fdea37-8a57-41d7-88f8-03fef0a28e40
-- title:
--   Scaling factor $H = N/e$
-- statement:
--   The potential uses the fixed scaling factor
--   $$
--   H = \frac{N}{e},
--   $$
--   where $N$ is the number of advertisers.
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.2, p.4

import Mathlib

namespace OnlineBudgetAlloc

/-- The scaling factor `H := N/e` of the potential (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.2, p.4). -/
noncomputable def Hscale (N : ℕ) : ℝ := (N : ℝ) / Real.exp 1

end OnlineBudgetAlloc


