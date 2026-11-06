-- Prove2me | Definitions.Def_ParetoNCSched_mrcCost
-- name    : ParetoNCSched_mrcCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:21:01.991013+00:00
-- url     : https://prove2.me/theorems/cd391360-3381-484a-80de-ce1d429a8d37
-- title:
--   The cost $\mathrm{MRC}_R(p,\sigma)$ of the algorithm
-- statement:
--   $\mathrm{MRC}_R(p,\sigma)\in[0,\infty]$ is the total completion time $\sum_j C_j$ of the run of $\mathrm{MRC}_R$ on sizes $p$ with predicted order $\sigma$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15

import Mathlib
import Definitions.Def_ParetoNCSched_mrcRate
import Definitions.Def_ParetoNCSched_totalCompletion
open scoped ENNReal

namespace ParetoNCSched

/-- **The cost `MRC_R(p, σ)`**: the total completion time of the run of `MRC_R` on sizes `p` with
predicted order `σ`. Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15 ("Writing A(p, σ) for the total completion time
of the run of A on sizes p with prediction σ").

**Formalization Note.** In `ℝ≥0∞`; a job that never completes contributes `⊤`. -/
noncomputable def mrcCost {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ≥0∞ :=
  totalCompletion p (mrcRate R p σ)

end ParetoNCSched


