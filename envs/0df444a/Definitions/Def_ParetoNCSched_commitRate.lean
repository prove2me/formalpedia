-- Prove2me | Definitions.Def_ParetoNCSched_commitRate
-- name    : ParetoNCSched_commitRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:57.818451+00:00
-- url     : https://prove2.me/theorems/30350318-29c5-4570-9b84-d9bfa6f27f17
-- title:
--   The rate $a$ of the committed job
-- statement:
--   The committed job runs at rate
--   $$a=\begin{cases}1 & \text{in the commit branch},\\[2pt] \dfrac{\gamma_r-N/R}{\gamma_r-\gamma_c} & \text{in the mixing branch},\end{cases}$$
--   the mixing value being the solution of $a\gamma_c+(1-a)\gamma_r=N/R$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, lines 6–9, p.9

import Mathlib
import Definitions.Def_ParetoNCSched_IsCommit
import Definitions.Def_ParetoNCSched_gammaR

namespace ParetoNCSched

/-- **The rate `a` of the committed job.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, lines 6–9, p.9: `a ← 1` in the commit
branch, and `a ← (γ_r − N/R)/(γ_r − γ_c)` in the mixing branch. -/
noncomputable def commitRate {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (s : MState n) (j : Fin n) : ℝ :=
  haveI := Classical.propDecidable (IsCommit R p s j)
  if IsCommit R p s j then 1
  else (gammaR p s j - ((unfinished p s).card : ℝ) / R) / (gammaR p s j - gammaC s j)

end ParetoNCSched


