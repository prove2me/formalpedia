-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_AlgRunState
-- name    : ParetoNCSched_Supplement_AlgRunState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:26:17.817209+00:00
-- url     : https://prove2.me/theorems/1e0e2c57-108b-4e2f-be39-de997dbbddaa
-- title:
--   State of the run of a deterministic algorithm after a completion
-- statement:
--   The run of a deterministic algorithm is built completion by completion. After the $k$-th completion event its state consists of the completion history $H_k$, the time $C_k$ of the last completion ($C_0=0$), and the rate function of the run before $C_k$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15

import Mathlib

namespace ParetoNCSched.Supplement

/-- **State of the run of a deterministic algorithm after a completion.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A,
Model, p.15: "The run is defined by induction over completions: after the k-th completion, the
algorithm follows the rate function of the current history until the next completion."

The state after the `k`-th completion event records the completion history `hist`
`= ((j1, C1), …)`, the time `last` `= C_k` of the last completion (`C_0 = 0`), and `rate`, the
rate function of the run, used on `[0, C_k)`.

**Formalization Note.** The rate function of the run so far is stored as a function on `ℝ`;
only its values on `[0, last)` are used. -/
structure AlgRunState (n : ℕ) where
  /-- the completion history -/
  hist : List (Fin n × ℝ)
  /-- the time of the last completion -/
  last : ℝ
  /-- the run's rate function, used before `last` -/
  rate : ℝ → Fin n → ℝ

end ParetoNCSched.Supplement


