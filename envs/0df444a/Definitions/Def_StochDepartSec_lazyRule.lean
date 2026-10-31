-- Prove2me | Definitions.Def_StochDepartSec_lazyRule
-- name    : StochDepartSec_lazyRule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:34.87229+00:00
-- url     : https://prove2.me/theorems/26362d9b-909b-4fa5-b495-97011cf89e89
-- title:
--   Decision function of the optimal lazy policy
-- statement:
--   The **lazy rule** accepts at time $t$ with $k$ arrivals iff rejecting is strictly worse than accepting:
--
--   $$
--   \Theta^{\mathrm{lazy}}(t,k)=1\iff V(t,k)<\frac kn .
--   $$
--
--   By Observation 7 the optimal lazy policy accepts a departing best-so-far candidate iff $\Pr[\mathrm{success}(\mathrm{rej}_t)\mid\mathrm{hist}_t=h]<\Pr[\mathrm{success}(\mathrm{acc}_t)\mid\mathrm{hist}_t=h]$, and by Observation 8 the right side is $k/n$. Ties are rejected ("lazy").
--
--   **Formalization Note** $k/n$ is real division ($0$ when $n=0$, a case with no candidates).
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, §3, p.6 (lazy policies); Observations 7 and 8, p.7

import Mathlib
import Definitions.Def_StochDepartSec_rejValue
open MeasureTheory

namespace StochDepartSec

/-- The decision function of the optimal lazy policy: accept (`true`) at time `t` with `k`
arrivals iff rejecting is strictly worse than accepting, i.e. `rejValue(t, k) < k/n`.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, §3, p.6: "A policy is lazy if it rejects whenever at a time of departure acceptance and
rejection have identical conditional success probabilities"; Observation 7, p.7: "opt accepts this
candidate if and only if it has not accepted any candidate before and
Pr[success(rej_t) | hist_t = h] < Pr[success(acc_t) | hist_t = h]"; Observation 8, p.7:
"Pr[success(acc_t) | hist_t = h] = k/n".

**Formalization Note** `k/n` is real division; for `n = 0` it is `0` and the rule rejects, which
is never read (there are no candidates). At the probability-zero states of `rejValue` the rule
accepts for `k ≥ 1`. -/
noncomputable def lazyRule (n : ℕ) (A L : Measure ℝ) [IsProbabilityMeasure A]
    [IsProbabilityMeasure L] (t : ℝ) (k : ℕ) : Bool :=
  decide (rejValue n A L t k < (k : ℝ) / n)

end StochDepartSec


