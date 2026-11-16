-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_PredModel
-- name    : ParetoNCSched_Supplement_PredModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:24:13.072209+00:00
-- url     : https://prove2.me/theorems/9ce80463-7132-473e-9b45-f323d4e3dc15
-- title:
--   Prediction models: predictions, allowed predictions, correctness
-- statement:
--   A **prediction model** fixes, for every number $n$ of jobs, the set of predictions an algorithm may receive, which of them are allowed, and when a prediction $y$ is **correct** for the job sizes $p\in(0,\infty)^n$.
--
--   The paper has two models: predicted orders (a permutation $\sigma$, correct if $p_{\sigma(1)}\le\dots\le p_{\sigma(n)}$) and predicted sizes (a vector $y\in(0,\infty)^n$, correct if $y=p$). Consistency, robustness and the deterministic frontier are defined uniformly over a model.
--
--   **Formalization Note** A structure with a type family `Pred n`, a predicate `Adm` and a predicate `Correct p y`.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Section 2, p.7; Appendix A, Model, p.15; Appendix E, Predicted sizes, p.31

import Mathlib

namespace ParetoNCSched.Supplement

/-- **A prediction model.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Section 2, p.7, Appendix A, Model, p.15, and Appendix E,
"Predicted sizes", p.31: "The prediction is either an order σ of the jobs, which is correct if
p_σ(1) ≤ ⋯ ≤ p_σ(n), or a vector of sizes y, which is correct if y = p."

A prediction model records, for every number of jobs `n`, the type `Pred n` of predictions an
algorithm may receive, the predicate `Adm` singling out the predictions the paper allows (all
orders; size vectors in `(0, ∞)ⁿ`), and the predicate `Correct p y` saying that the prediction
`y` is correct for the sizes `p`.

**Formalization Note.** The two models of the paper are `orderModel` and `sizeModel`. -/
structure PredModel where
  /-- the predictions for `n` jobs -/
  Pred : ℕ → Type
  /-- the predictions the paper allows -/
  Adm : {n : ℕ} → Pred n → Prop
  /-- correctness of a prediction for the sizes `p` -/
  Correct : {n : ℕ} → (Fin n → ℝ) → Pred n → Prop

end ParetoNCSched.Supplement


