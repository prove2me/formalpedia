-- Prove2me | Definitions.Def_ParetoNCSched_stepRates
-- name    : ParetoNCSched_stepRates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:13.264081+00:00
-- url     : https://prove2.me/theorems/cd50ac2b-aaa1-44ed-97e7-10151d4f8902
-- title:
--   Rates used by $\mathrm{MRC}_R$ from a state
-- statement:
--   The rates used by $\mathrm{MRC}_R$ from a state: with $N\ge2$, the committed job at rate $a$ and each waiting job at rate $b$; with $N=1$, the last job alone at rate $1$; with no unfinished job, all rates $0$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, lines 3 and 10, p.9; Appendix B, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_committedJob
import Definitions.Def_ParetoNCSched_commitRate
import Definitions.Def_ParetoNCSched_mixRates

namespace ParetoNCSched

/-- **The rate vector used from a state.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, lines 3 and 10, p.9, and Appendix B,
p.17: with `N ≥ 2`, `j` runs at rate `a` and each waiting job at rate `b`; with `N = 1`, "the last job
runs alone until it completes"; with no unfinished job, nothing runs. -/
noncomputable def stepRates {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (s : MState n) :
    Fin n → ℝ :=
  match committedJob p σ s with
  | none => 0
  | some j =>
    if (unfinished p s).card = 1 then Pi.single j 1
    else mixRates p s j (commitRate R p s j)

end ParetoNCSched


