-- Prove2me | Definitions.Def_BayesBAI_simpleRegret
-- name    : BayesBAI_simpleRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:58:02.303313+00:00
-- url     : https://prove2.me/theorems/8a6989ed-6f2f-4b22-9303-26f9a40590b5
-- title:
--   The simple regret $\mathrm R_\mu(T)$ of two-stage exploration
-- statement:
--   The frequentist simple regret of Algorithm 1 at means $\mu$ is
--   $$
--   \mathrm R_\mu(T)=\mu^*-\mathbb E_\mu[\mu_{J(T)}].
--   $$
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, eq. (2), p.1

import Mathlib
import Definitions.Def_BayesBAI_recommend
import Definitions.Def_BayesBAI_tapeExp
import Definitions.Def_BayesBAI_bestMean

namespace BayesBAI

/-- The frequentist simple regret `R_μ(T) = μ* - 𝔼_μ[μ_{J(T)}]` of Algorithm 1, (2), Komiyama, Ariu,
Kato, Qin, arXiv:2111.09885v3, p.1. -/
noncomputable def simpleRegret {K : ℕ} (hK : 2 ≤ K) (sel : TieBreak K) (q : ℝ) (T : ℕ)
    (μ : Fin K → ℝ) : ℝ :=
  bestMean hK μ - tapeExp μ (fun ω : Tape K T => μ (recommend sel q ω))

end BayesBAI


