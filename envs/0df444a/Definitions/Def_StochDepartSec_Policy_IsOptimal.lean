-- Prove2me | Definitions.Def_StochDepartSec_Policy_IsOptimal
-- name    : StochDepartSec_Policy_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:59:36.272499+00:00
-- url     : https://prove2.me/theorems/7b804d3b-8714-4ff5-8e91-d332f095a680
-- title:
--   Optimal policy
-- statement:
--   A policy is **optimal** for $(n,\mathcal A,\mathcal L)$ if it is admissible and
--
--   $$
--   \Pr[\mathrm{success}(q)]\le\Pr[\mathrm{success}(\mathrm{pol})]\qquad\text{for every admissible policy }q.
--   $$
--
--   The comparison is against all admissible policies: history-dependent, randomized, and label-aware.
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, §2, p.5; Theorem 1, p.6

import Mathlib
import Definitions.Def_StochDepartSec_Policy
import Definitions.Def_StochDepartSec_Policy_Admissible
import Definitions.Def_StochDepartSec_Policy_successProb
open MeasureTheory

namespace StochDepartSec

/-- A policy is optimal for the instance `(n, A, L)` if it is admissible and no admissible policy
has a larger success probability.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, §3, p.6: "an optimal policy for the stochastic departure secretary problem"; §2, p.5: "maximizes
the probability of selecting the best candidate".

**Formalization Note** Optimality is stated against every admissible policy (history-dependent,
randomized, label-aware), not through a supremum value. -/
def Policy.IsOptimal {n : ℕ} (pol : Policy n) (A L : Measure ℝ) [IsProbabilityMeasure A]
    [IsProbabilityMeasure L] : Prop :=
  pol.Admissible ∧ ∀ q : Policy n, q.Admissible → q.successProb A L ≤ pol.successProb A L

end StochDepartSec


