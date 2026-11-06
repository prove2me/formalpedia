-- Prove2me | Definitions.Def_ParetoNCSched_level
-- name    : ParetoNCSched_level
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:39.270793+00:00
-- url     : https://prove2.me/theorems/987c2108-7750-4c7b-b209-26d7893bd48b
-- title:
--   The level $\ell$: common elapsed time of the waiting jobs
-- statement:
--   The *level* $\ell$ is the common elapsed time of the $N-1$ waiting jobs.
--
--   **Formalization Note** $\ell$ is defined as the minimum elapsed time over the waiting jobs; Lemma B.1(a) states that the waiting jobs always share one elapsed time, so this minimum is the common value. With no waiting job ($N\le1$, where the algorithm does not use $\ell$) the value is $0$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, line 4, p.9

import Mathlib
import Definitions.Def_ParetoNCSched_waiting

namespace ParetoNCSched

/-- **The level `ℓ`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 1, line 4, p.9: "ℓ ← the common elapsed time of the N − 1
waiting jobs".

**Formalization Note.** The level is the **minimum** elapsed time over the waiting jobs; Lemma B.1(a)
states that the waiting jobs share one elapsed time, so this is the common value. With no waiting
job (`N ≤ 1`, where the algorithm never uses `ℓ`) the value is `0`. -/
noncomputable def level {n : ℕ} (p : Fin n → ℝ) (s : MState n) (j : Fin n) : ℝ :=
  if h : (waiting p s j).Nonempty then (waiting p s j).inf' h s.e else 0

end ParetoNCSched


