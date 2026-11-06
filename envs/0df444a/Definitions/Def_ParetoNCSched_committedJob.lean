-- Prove2me | Definitions.Def_ParetoNCSched_committedJob
-- name    : ParetoNCSched_committedJob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:31.382017+00:00
-- url     : https://prove2.me/theorems/96d2aa18-b2e4-4e72-b6f5-f5f720f83832
-- title:
--   The committed job: first unfinished job in the predicted order
-- statement:
--   The *committed job* $j$ is the first unfinished job in the predicted order $\sigma$: $j=\sigma(k_0)$ with $k_0$ the least position whose job is unfinished.
--
--   **Formalization Note** Positions are 0-based; the value is "none" when every job is completed.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, line 2, p.9; Appendix B, Notation, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_unfinished

namespace ParetoNCSched

/-- **The committed job `j`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, line 2, p.9, and Appendix B, Notation, p.17:
"the committed job j is the first unfinished job in σ".

**Formalization Note.** `σ k` is the job at (0-based) position `k`; the committed job is `σ k₀`
with `k₀` the least position whose job is unfinished. It is `none` when no job is unfinished. -/
noncomputable def committedJob {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (s : MState n) :
    Option (Fin n) :=
  if h : (Finset.univ.filter fun k => σ k ∈ unfinished p s).Nonempty then
    some (σ ((Finset.univ.filter fun k => σ k ∈ unfinished p s).min' h))
  else none

end ParetoNCSched


