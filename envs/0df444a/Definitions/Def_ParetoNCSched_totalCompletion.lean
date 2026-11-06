-- Prove2me | Definitions.Def_ParetoNCSched_totalCompletion
-- name    : ParetoNCSched_totalCompletion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:37.267081+00:00
-- url     : https://prove2.me/theorems/99ebb598-e80b-481c-88f1-d82d8afa3ee5
-- title:
--   Total completion time $\sum_j C_j$ of a rate function
-- statement:
--   The cost of a rate function $r$ on sizes $p$ is the total completion time
--   $$\sum_{j} C_j\in[0,\infty],$$
--   which is $+\infty$ as soon as one job never completes.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Section 1, p.3; Appendix A, Model, p.15

import Mathlib
import Definitions.Def_ParetoNCSched_complTime
open scoped ENNReal

namespace ParetoNCSched

/-- **Total completion time `Σⱼ Cⱼ`** of a rate function on sizes `p`. Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Section 1, p.3 ("minimize
the sum of their completion times Σⱼ Cⱼ") and Appendix A, p.15 (`A(p, σ)` is the total completion
time of the run).

**Formalization Note.** The sum is in `ℝ≥0∞`; it is `⊤` as soon as one job never completes. -/
noncomputable def totalCompletion {n : ℕ} (p : Fin n → ℝ) (r : ℝ → Fin n → ℝ) : ℝ≥0∞ :=
  ∑ j, complTime p r j

end ParetoNCSched


