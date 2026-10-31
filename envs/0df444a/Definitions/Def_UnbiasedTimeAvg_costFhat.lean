-- Prove2me | Definitions.Def_UnbiasedTimeAvg_costFhat
-- name    : UnbiasedTimeAvg_costFhat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:19.959514+00:00
-- url     : https://prove2.me/theorems/552cdba2-a3c0-401d-bc60-cfdaf1193ce0
-- title:
--   The expected cost $\hat T_k=k+qT_k$ of $\hat f_k$
-- statement:
--   Since $f_{k,0}$ costs $k$ and $Z'_k$ is simulated with probability $q$, the expected time to simulate $\hat f_k$ is
--   $$\hat T_k=k+qT_k.$$
--
--   **Formalization Note** As for $T_k$, the paper's cost model taken as the definition.
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), p.9 (T̂_k = k + qT_k)

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_costZ

namespace UnbiasedTimeAvg

/-- **The expected time `T̂_k` to simulate `f̂_k`, under the paper's cost model.**
Kahalé, arXiv:2209.09581v1, p.9: "Let `T̂_k` be the expected time to simulate `f̂_k`. As the
expected time to simulate `f_{k,0}` is equal to `k`, we have `T̂_k = k + qT_k`."

`costFhat p q k = k + q · T_k`.

**Formalization Note.** As for `costZ`, this is the paper's stated cost model taken as the
definition. -/
noncomputable def costFhat (p : ℕ → ℝ) (q : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) + q * costZ p k

end UnbiasedTimeAvg


