-- Prove2me | Definitions.Def_ParetoNCSched_waitRate
-- name    : ParetoNCSched_waitRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:59.921202+00:00
-- url     : https://prove2.me/theorems/58063a78-6d14-4177-a3f4-3a6fefe5e4e3
-- title:
--   The rate $b=(1-a)/(N-1)$ of each waiting job
-- statement:
--   Each waiting job runs at rate
--   $$b=\frac{1-a}{N-1}.$$
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, line 10, p.9; Appendix B, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_commitRate

namespace ParetoNCSched

/-- **The rate `b` of each waiting job.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, line 10, p.9, and Appendix B, p.17:
"each waiting job at rate b = (1 − a)/(N − 1)". -/
noncomputable def waitRate {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (s : MState n) (j : Fin n) : ℝ :=
  (1 - commitRate R p s j) / (((unfinished p s).card : ℝ) - 1)

end ParetoNCSched


