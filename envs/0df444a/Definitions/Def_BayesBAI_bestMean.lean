-- Prove2me | Definitions.Def_BayesBAI_bestMean
-- name    : BayesBAI_bestMean
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:56.901991+00:00
-- url     : https://prove2.me/theorems/149f776d-01a4-4553-b03b-1550f64e73df
-- title:
--   The best mean $\mu^*$
-- statement:
--   $\mu^*=\max_{i\in[K]}\mu_i$ is the mean of the best arm.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, §1, p.1

import Mathlib

namespace BayesBAI

/-- `μ* = max_i μ_i`, the mean of the best arm, Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.1.

**Formalization Note.** The maximum is `Finset.sup'` over all arms, nonempty as `2 ≤ K`. -/
noncomputable def bestMean {K : ℕ} (hK : 2 ≤ K) (μ : Fin K → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ μ

end BayesBAI


