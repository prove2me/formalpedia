-- Prove2me | Definitions.Def_ParetoNCSched_betR
-- name    : ParetoNCSched_betR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:29.311443+00:00
-- url     : https://prove2.me/theorems/85b4c406-0387-490d-ad86-017154f2fec8
-- title:
--   The constant $\beta=(R-2)/(R+2)$ of (14)
-- statement:
--   $$\beta=\frac{R-2}{R+2}.$$
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, Eq. (14), p.28

import Mathlib

namespace ParetoNCSched

/-- **The constant `β = (R − 2)/(R + 2)`** of (14). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix D.3, (14), p.28. -/
noncomputable def betR (R : ℝ) : ℝ :=
  (R - 2) / (R + 2)

end ParetoNCSched


