-- Prove2me | Definitions.Def_BayesBAI_firstPulls
-- name    : BayesBAI_firstPulls
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:50.658733+00:00
-- url     : https://prove2.me/theorems/fb3d6881-6839-4ab2-81fb-15a39cf52526
-- title:
--   The first-stage sample size $n_1=\lceil qT/K\rceil$
-- statement:
--   In the first stage of Algorithm 1, each arm is drawn $n_1=\lceil qT/K\rceil$ times.
--
--   **Formalization Note.** The paper writes "$qT/K$ times" without rounding. The ceiling keeps the exact constant of Lemma 2.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Algorithm 1, p.6

import Mathlib

namespace BayesBAI

/-- `n₁ = ⌈qT/K⌉`, the number of pulls of each arm in the first stage of Algorithm 1, Komiyama, Ariu,
Kato, Qin, arXiv:2111.09885v3, p.6.

**Formalization Note.** The paper does not round `qT/K`. The ceiling keeps Lemma 2's exact constant
(the Hoeffding exponent is `2 n₁ B_conf²`, which must be at least `2 log T`). -/
noncomputable def firstPulls (K : ℕ) (q : ℝ) (T : ℕ) : ℕ :=
  ⌈q * T / K⌉₊

end BayesBAI


