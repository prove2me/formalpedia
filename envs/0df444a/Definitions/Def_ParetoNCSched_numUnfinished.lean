-- Prove2me | Definitions.Def_ParetoNCSched_numUnfinished
-- name    : ParetoNCSched_numUnfinished
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:09.932454+00:00
-- url     : https://prove2.me/theorems/0bf5fd67-0b2d-4a8b-b40f-e06acbe5f067
-- title:
--   Number of unfinished jobs $N(t)=|\{j: C_j>t\}|$
-- statement:
--   For a rate function $r$ on sizes $p$, the number of unfinished jobs at time $t$ is
--   $$N(t)=\big|\{j:\ C_j>t\}\big| .$$
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Notation, p.15

import Mathlib
import Definitions.Def_ParetoNCSched_complTime
open scoped ENNReal

namespace ParetoNCSched

/-- **Number of unfinished jobs `N(t)`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Notation, p.15: "N(t) = |{j : Cⱼ > t}|".

**Formalization Note.** `Cⱼ ∈ ℝ≥0∞` is compared with `ENNReal.ofReal t`; the paper uses `t ≥ 0`. -/
noncomputable def numUnfinished {n : ℕ} (p : Fin n → ℝ) (r : ℝ → Fin n → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun j => ENNReal.ofReal t < complTime p r j).card

end ParetoNCSched


