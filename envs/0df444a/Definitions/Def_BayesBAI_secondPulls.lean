-- Prove2me | Definitions.Def_BayesBAI_secondPulls
-- name    : BayesBAI_secondPulls
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:36.990793+00:00
-- url     : https://prove2.me/theorems/a73f4d4d-9444-4d14-b93a-e0bd25e4e365
-- title:
--   The second-stage sample size $n_2(s)$
-- statement:
--   In the second stage of Algorithm 1, each of the $s$ candidates is drawn $n_2(s)=\lfloor (T-Kn_1)/s\rfloor$ times.
--
--   **Formalization Note.** The paper writes "$(1-q)T/|\hat{\mathcal J}^*|$ times" without rounding. Here the budget left by the first stage is shared equally and rounded down. The subtraction is truncated at $0$, which happens only when $Kn_1>T$, and large $T$ excludes that.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Algorithm 1, p.6

import Mathlib
import Definitions.Def_BayesBAI_firstPulls

namespace BayesBAI

/-- `n₂(s) = ⌊(T - K n₁)/s⌋`, the number of second-stage pulls of each of the `s` candidates in
Algorithm 1, Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.6.

**Formalization Note.** The paper does not round `(1 - q)T/|Ĵ*|`. The budget left after the first stage
is `T - K n₁`, shared equally and rounded down. The subtraction and division are natural-number
operations; subtraction truncates only when `K n₁ > T`, which large `T` excludes. -/
noncomputable def secondPulls (K : ℕ) (q : ℝ) (T s : ℕ) : ℕ :=
  (T - K * firstPulls K q T) / s

end BayesBAI


