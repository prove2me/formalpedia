-- Prove2me | Definitions.Def_ParetoNCSched_qFun
-- name    : ParetoNCSched_qFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:33.991037+00:00
-- url     : https://prove2.me/theorems/db748b97-23a4-48d4-bee1-eeda7ab98b9b
-- title:
--   The function $q(\xi)=\frac{(1-\xi)^2-(R-1)}{2}$ of (9)
-- statement:
--   $$q(\xi)=\frac{(1-\xi)^2-(R-1)}{2}.$$
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.2, Eq. (9), p.24

import Mathlib

namespace ParetoNCSched

/-- **The function `q`** of (9). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.2, (9), p.24: "q(ξ) = ((1 − ξ)² − (R − 1))/2". -/
noncomputable def qFun (R ξ : ℝ) : ℝ :=
  ((1 - ξ) ^ 2 - (R - 1)) / 2

end ParetoNCSched


