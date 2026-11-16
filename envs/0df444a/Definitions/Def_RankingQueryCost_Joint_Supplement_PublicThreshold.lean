-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Supplement_PublicThreshold
-- name    : RankingQueryCost_Joint_Supplement_PublicThreshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:46:31.38417+00:00
-- url     : https://prove2.me/theorems/4485d15a-50f3-45dd-bd94-be11d4d5e352
-- title:
--   Worst complete-table compatible-set radius
-- statement:
--   For each complete comparison table $T$ with nonempty compatible set $C_s(T)$, let $\rho_s(T)$ be its squared radius with continuous centers in $Q$. Define
--
--   $$M_{\rm pub}(n,s)=\sup_{T:C_s(T)\ne\varnothing}\rho_s(T).$$
--
--   The finite table space makes this supremum a maximum. The definition uses extended nonnegative reals; a clean table always supplies a nonempty compatible set. This quantity measures full-information public uncertainty, rather than an acquisition budget.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §2.2, p. 4, PDF p. 5

import Definitions.Def_RankingQueryCost_Joint_Supplement_Radius

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint.Supplement

/-- §2.2: maximum complete-table radius, ranging only over nonempty version spaces.
There are finitely many tables; no asymptotic rate is built into this definition. -/
def publicThreshold (n s : ℕ) : ENNReal :=
  ⨆ T : {T : Tournament n // (compatible s (completeTranscript T)).Nonempty}, radius s T.val

end RankingQueryCost.Joint.Supplement


