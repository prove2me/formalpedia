-- Prove2me | Definitions.Def_BayesBAI_lcb
-- name    : BayesBAI_lcb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:55:12.656059+00:00
-- url     : https://prove2.me/theorems/dd0accdc-1c77-4f30-9a3a-5a8b60d1c618
-- title:
--   The lower confidence bound $L_i$
-- statement:
--   At the end of the first stage, $L_i=\hat\mu_{i,n_1}-B_{\mathrm{conf}}$.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Algorithm 1, p.6

import Mathlib
import Definitions.Def_BayesBAI_Bconf
import Definitions.Def_BayesBAI_empMean
import Definitions.Def_BayesBAI_firstPulls

namespace BayesBAI

/-- The lower confidence bound `L_i = μ̂_i(qT) - B_conf` at the end of the first stage of
Algorithm 1, Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.6. -/
noncomputable def lcb {K T : ℕ} (q : ℝ) (ω : Tape K T) (i : Fin K) : ℝ :=
  empMean ω i (firstPulls K q T) - Bconf K q T

end BayesBAI


