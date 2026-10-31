-- Prove2me | Definitions.Def_SteinerCutDominants_gamma
-- name    : SteinerCutDominants_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:13.667622+00:00
-- url     : https://prove2.me/theorems/6adc82a0-519d-4a27-9ccf-ca7614a7b935
-- title:
--   The right-hand side $\gamma_c(G,T)$ of a weighted Steiner graph
-- statement:
--   For a weighted Steiner graph $((G,T),c)$, the number $\gamma_c(G,T)$, the minimum $c$-weight of a $T$-Steiner cut. The paper calls it the **right-hand side** of $c$.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §2, p.4

import Mathlib
import Definitions.Def_SteinerCutDominants_WSG_wR
import Definitions.Def_SteinerCutDominants_gammaOf

namespace SteinerCutDominants

/-- `γ_c(G, T)`, the right-hand side of the weight vector of a weighted Steiner graph (Conforti,
Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, §2, p.4). -/
noncomputable def gamma (H : WSG) : ℝ := gammaOf H.G H.T H.wR

end SteinerCutDominants


