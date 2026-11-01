-- Prove2me | Definitions.Def_BayesBAI_goodEvent
-- name    : BayesBAI_goodEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:56:10.075729+00:00
-- url     : https://prove2.me/theorems/f63626d7-3b80-41cf-aeea-420af0a4b938
-- title:
--   The event $\mathcal S$ of (9)
-- statement:
--   $\mathcal S$ is the event that the true parameters lie within the confidence bounds:
--   $$
--   \mathcal S=\bigcap_{i\in[K]}\{L_i\le\mu_i\le U_i\}.
--   $$
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, eq. (9), p.7

import Mathlib
import Definitions.Def_BayesBAI_lcb
import Definitions.Def_BayesBAI_ucb

namespace BayesBAI

/-- The event `𝒮 = ⋂_i {L_i ≤ μ_i ≤ U_i}` of (9), Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3,
p.7. -/
def goodEvent {K T : ℕ} (q : ℝ) (μ : Fin K → ℝ) (ω : Tape K T) : Prop :=
  ∀ i, lcb q ω i ≤ μ i ∧ μ i ≤ ucb q ω i

end BayesBAI


