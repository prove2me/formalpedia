-- Prove2me | Definitions.Def_ParetoNCSched_IsCommit
-- name    : ParetoNCSched_IsCommit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:22.65438+00:00
-- url     : https://prove2.me/theorems/8081930e-5d80-43be-ac22-1af73e7bdf74
-- title:
--   The commit branch: $D<0$ or $\gamma_c\ge N/R$
-- statement:
--   At an event time, $\mathrm{MRC}_R$ is in the *commit branch* if
--   $$D<0\quad\text{or}\quad \gamma_c\ge \frac NR,$$
--   and in the *mixing branch* otherwise.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, line 6, p.9

import Mathlib
import Definitions.Def_ParetoNCSched_gammaC
import Definitions.Def_ParetoNCSched_slack
import Definitions.Def_ParetoNCSched_unfinished

namespace ParetoNCSched

/-- **The commit branch.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, line 6, p.9: "if D < 0 or γ_c ≥ N/R then" (committing is
safe); otherwise the mixing branch. -/
def IsCommit {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (s : MState n) (j : Fin n) : Prop :=
  slack R s < 0 ∨ ((unfinished p s).card : ℝ) / R ≤ gammaC s j

end ParetoNCSched


