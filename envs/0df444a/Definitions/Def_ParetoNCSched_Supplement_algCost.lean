-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_algCost
-- name    : ParetoNCSched_Supplement_algCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:30:44.563622+00:00
-- url     : https://prove2.me/theorems/99ad64af-701c-412c-a6f1-d52c71b9cd19
-- title:
--   The cost $A(p,y)$ of a deterministic algorithm
-- statement:
--   $A(p,y)$ is the total completion time $\sum_j C_j$ of the run of $A$ on sizes $p$ with prediction $y$, where $C_j=\inf\{t\ge0: e_j(t)\ge p_j\}$.
--
--   **Formalization Note** In $[0,\infty]$: a job that never completes has $C_j=\infty$, and then $A(p,y)=\infty$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_algRate
import Definitions.Def_ParetoNCSched_totalCompletion
open scoped ENNReal

namespace ParetoNCSched.Supplement

/-- **The cost `A(p, y)` of a deterministic algorithm.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15: "Writing
A(p, σ) for the total completion time of the run of A on sizes p with prediction σ".

**Formalization Note.** The base mission's `totalCompletion` of the run, in `ℝ≥0∞`: a job that
never completes has `C_j = ⊤`, and then `A(p, y) = ⊤`. -/
noncomputable def algCost {M : PredModel} (A : DetAlg M) {n : ℕ} (p : Fin n → ℝ)
    (y : M.Pred n) : ℝ≥0∞ :=
  totalCompletion p (algRate A p y)

end ParetoNCSched.Supplement


