-- Prove2me | Definitions.Def_ParetoNCSched_gammaR
-- name    : ParetoNCSched_gammaR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:32.205518+00:00
-- url     : https://prove2.me/theorems/0eefa7c9-1887-4e81-af73-62327045748c
-- title:
--   The Round-Robin rate $\gamma_r=1+|\{i\ne j: e_i>\ell\}|+N/2$
-- statement:
--   With committed job $j$, level $\ell$ and $N$ unfinished jobs,
--   $$\gamma_r=1+\big|\{i\neq j:\ e_i>\ell\}\big|+\frac N2,$$
--   where completed jobs are included in the count. It is the rate at which $\Phi(e)$ grows when the waiting jobs share the machine equally.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, line 5, p.9; Appendix B, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_level

namespace ParetoNCSched

/-- **The Round-Robin rate `γ_r`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, line 5, p.9, and Appendix B, p.17:
"γ_r = 1 + |{i ≠ j : eᵢ > ℓ}| + N/2", where the count includes completed jobs and `N/2` is real. -/
noncomputable def gammaR {n : ℕ} (p : Fin n → ℝ) (s : MState n) (j : Fin n) : ℝ :=
  1 + ((Finset.univ.filter fun i => i ≠ j ∧ level p s j < s.e i).card : ℝ) +
    ((unfinished p s).card : ℝ) / 2

end ParetoNCSched


