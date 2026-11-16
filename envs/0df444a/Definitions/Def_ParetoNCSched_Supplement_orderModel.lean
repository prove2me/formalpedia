-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_orderModel
-- name    : ParetoNCSched_Supplement_orderModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:24:46.270581+00:00
-- url     : https://prove2.me/theorems/a69ceea1-f6da-4154-acec-bee2a5314eb9
-- title:
--   The predicted-order model
-- statement:
--   In the **predicted-order model** a prediction for $n$ jobs is a permutation $\sigma$ of the jobs. Every permutation is allowed, and $\sigma$ is correct for the sizes $p$ if
--
--   $$p_{\sigma(1)}\le p_{\sigma(2)}\le\dots\le p_{\sigma(n)}.$$
--
--   This is the model in which the paper's upper bound is attained and one of the two models of the lower bound (Theorem E.2).
--
--   **Formalization Note** Correctness is the base mission's `IsCorrect` (0-based positions, `σ k` the job at position `k`).
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_PredModel
import Definitions.Def_ParetoNCSched_IsCorrect

namespace ParetoNCSched.Supplement

/-- **The predicted-order model.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15: "The prediction is a permutation
σ of the jobs, a predicted order; it is correct if p_σ(1) ≤ ⋯ ≤ p_σ(n)."

**Formalization Note.** Every permutation is an allowed prediction; correctness is the base
mission's `ParetoNCSched.IsCorrect` (0-based positions, `σ k` the job at position `k`). -/
def orderModel : PredModel where
  Pred n := Equiv.Perm (Fin n)
  Adm _ := True
  Correct p σ := IsCorrect p σ

end ParetoNCSched.Supplement


