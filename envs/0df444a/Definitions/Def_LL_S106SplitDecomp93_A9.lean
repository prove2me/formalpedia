-- Prove2me | Definitions.Def_LL_S106SplitDecomp93_A9
-- name    : LL_S106SplitDecomp93_A9
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T18:04:26.847812+00:00
-- url     : https://prove2.me/theorems/6dc8f4e8-c385-479f-a489-eadbdb4b3080
-- title:
--   The scaled constant $A_9(\lambda)=4A_3\lambda^{1/2}$
-- statement:
--   For real $\lambda$, $A_9(\lambda)=4A_3\lambda^{1/2}$ with the real power.

import Mathlib
import Definitions.Def_LL_S106SplitDecomp93_A3

namespace LL_S106SplitDecomp93

noncomputable section

open Real

def A9 (lam : ℝ) : ℝ := 4 * A3 * lam ^ (1 / 2 : ℝ)

end

end LL_S106SplitDecomp93


