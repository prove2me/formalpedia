-- Prove2me | Definitions.Def_ParetoNCSched_alpR
-- name    : ParetoNCSched_alpR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:31.584065+00:00
-- url     : https://prove2.me/theorems/fc6cb12e-2d5e-435b-8c1a-066f4ec81a59
-- title:
--   The constant $\alpha=1-\gamma=2/(R+2)$ of (14)
-- statement:
--   $$\alpha=1-\gamma=\frac{2}{R+2}.$$
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, Eq. (14), p.28

import Mathlib

namespace ParetoNCSched

/-- **The constant `α = 1 − γ = 2/(R + 2)`** of (14). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, (14), p.28. -/
noncomputable def alpR (R : ℝ) : ℝ :=
  2 / (R + 2)

end ParetoNCSched


