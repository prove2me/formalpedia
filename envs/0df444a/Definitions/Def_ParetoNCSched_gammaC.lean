-- Prove2me | Definitions.Def_ParetoNCSched_gammaC
-- name    : ParetoNCSched_gammaC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:23.626414+00:00
-- url     : https://prove2.me/theorems/06b98456-059d-463b-9baf-68da51e6de6b
-- title:
--   The commit rate $\gamma_c=1+|\{i: e_i>e_j\}|$
-- statement:
--   With committed job $j$,
--   $$\gamma_c=1+\big|\{i:\ e_i>e_j\}\big|,$$
--   where completed jobs are included in the count with elapsed time equal to their size. It is the rate at which $\Phi(e)$ grows when $j$ runs alone.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, line 5, p.9; Appendix B, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_MState

namespace ParetoNCSched

/-- **The commit rate `γ_c`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, line 5, p.9, and Appendix B, p.17:
"γ_c = 1 + |{i : eᵢ > eⱼ}|", where the count includes completed jobs. -/
noncomputable def gammaC {n : ℕ} (s : MState n) (j : Fin n) : ℝ :=
  1 + ((Finset.univ.filter fun i => s.e j < s.e i).card : ℝ)

end ParetoNCSched


