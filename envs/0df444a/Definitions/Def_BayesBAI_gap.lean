-- Prove2me | Definitions.Def_BayesBAI_gap
-- name    : BayesBAI_gap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:39.511103+00:00
-- url     : https://prove2.me/theorems/223febc3-37aa-4f3c-bf22-e3a634e82295
-- title:
--   The loss $\Delta_J=\mu^*-\mu_J$
-- statement:
--   $\Delta_J=\mu^*-\mu_J$ is the loss of recommending arm $J$.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, p.7

import Mathlib
import Definitions.Def_BayesBAI_bestMean

namespace BayesBAI

/-- `Δ_J = μ* - μ_J`, the loss of recommending arm `J`, Komiyama, Ariu, Kato, Qin,
arXiv:2111.09885v3, p.7. -/
noncomputable def gap {K : ℕ} (hK : 2 ≤ K) (μ : Fin K → ℝ) (J : Fin K) : ℝ :=
  bestMean hK μ - μ J

end BayesBAI


