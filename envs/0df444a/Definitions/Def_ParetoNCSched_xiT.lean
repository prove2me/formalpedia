-- Prove2me | Definitions.Def_ParetoNCSched_xiT
-- name    : ParetoNCSched_xiT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:29.393878+00:00
-- url     : https://prove2.me/theorems/01d87535-6dc5-452d-b1d4-561f79d45278
-- title:
--   The threshold $\tilde\xi=1/(1+R)$ of (9)
-- statement:
--   $$\tilde\xi=\frac{1}{1+R}.$$
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.2, Eq. (9), p.24

import Mathlib

namespace ParetoNCSched

/-- **The threshold `ξ̃ = 1/(1 + R)`** of (9). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.2, (9), p.24. -/
noncomputable def xiT (R : ℝ) : ℝ :=
  1 / (1 + R)

end ParetoNCSched


