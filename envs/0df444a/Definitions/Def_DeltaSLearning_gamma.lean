-- Prove2me | Definitions.Def_DeltaSLearning_gamma
-- name    : DeltaSLearning_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:26.668641+00:00
-- url     : https://prove2.me/theorems/c902084c-5400-4273-bf2f-8a836b928da0
-- title:
--   Per-period cost bound $\gamma=K+(h+c+p)\beta$
-- statement:
--   For parameters $(K,c,h,p,\beta,\rho)$, the constant
--   $$\gamma := K+(h+c+p)\beta .$$
--   It bounds the absolute pseudo cost of every period (Lemma 1) and is the scale of every constant in the regret analysis.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (10), p.12

import Mathlib
import Definitions.Def_DeltaSLearning_Params

namespace DeltaSLearning

/-- The per-period bound `γ := K + (h + c + p)β` of (10).
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), eq. (10),
p.12. -/
noncomputable def gamma (cp : Params) : ℝ :=
  cp.K + (cp.h + cp.c + cp.p) * cp.β

end DeltaSLearning


