-- Prove2me | Definitions.Def_LL_Task580_starWeight
-- name    : LL_Task580_starWeight
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T18:01:54.576322+00:00
-- url     : https://prove2.me/theorems/02efd5d6-8c06-4cb2-9eb4-05e3f77a5764
-- title:
--   The weight $\eta_*(t)=(\eta_2*_M\eta_{T2})(49t)$
-- statement:
--   For real $t$, $\eta_*(t)=\int_0^\infty \eta_2(y)\,\eta_{T2}(49t/y)\,dy/y$, where $\eta_{T2}(u)=u^2e^{-u^2/2}$ for $u>0$ and $0$ otherwise. It vanishes for $t\le0$.

import Mathlib
import Definitions.Def_LL_Task580_mconv
import Definitions.Def_LL_Task580_eta2
import Definitions.Def_LL_Task580_etaT2

namespace LL_Task580

noncomputable section

noncomputable def starWeight (t : ℝ) : ℝ :=
  mconv eta2 etaT2 (49 * t)

end

end LL_Task580


