-- Prove2me | Definitions.Def_BayesBAI_ucb
-- name    : BayesBAI_ucb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:54:45.003657+00:00
-- url     : https://prove2.me/theorems/e0535561-df0a-4227-a553-34d3be6ad0d7
-- title:
--   The upper confidence bound $U_i$
-- statement:
--   At the end of the first stage, $U_i=\hat\mu_{i,n_1}+B_{\mathrm{conf}}$.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Algorithm 1, p.6

import Mathlib
import Definitions.Def_BayesBAI_Bconf
import Definitions.Def_BayesBAI_empMean
import Definitions.Def_BayesBAI_firstPulls

namespace BayesBAI

/-- The upper confidence bound `U_i = μ̂_i(qT) + B_conf` at the end of the first stage of
Algorithm 1, Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.6. -/
noncomputable def ucb {K T : ℕ} (q : ℝ) (ω : Tape K T) (i : Fin K) : ℝ :=
  empMean ω i (firstPulls K q T) + Bconf K q T

end BayesBAI


