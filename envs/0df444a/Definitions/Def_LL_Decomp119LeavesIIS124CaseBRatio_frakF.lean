-- Prove2me | Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_frakF
-- name    : LL_Decomp119LeavesIIS124CaseBRatio_frakF
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:32:05.652462+00:00
-- url     : https://prove2.me/theorems/760eff07-55a4-449b-9eec-976ef997d28d
-- title:
--   The function $\mathfrak F(t)=e^{\gamma}\log\log t+2.50637/\log\log t$
-- statement:
--   For real $t$, $\mathfrak F(t)=e^{\gamma}\log\log t+2.50637/\log\log t$, where $\gamma$ is the Euler Mascheroni constant; it bounds $q/\varphi(q)$ in Helfgott's estimates.

import Mathlib

namespace LL_Decomp119LeavesIIS124CaseBRatio

noncomputable section

noncomputable def frakF (t : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * Real.log (Real.log t) +
    2.50637 / Real.log (Real.log t)

end

end LL_Decomp119LeavesIIS124CaseBRatio


