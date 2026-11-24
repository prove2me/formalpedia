-- Prove2me | Definitions.Def_LL_S106SplitDecomp93_A6
-- name    : LL_S106SplitDecomp93_A6
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T17:40:51.116934+00:00
-- url     : https://prove2.me/theorems/64ffff36-5d0f-408a-9dfb-b0effe34edf4
-- title:
--   The scaled constant $A_6(\lambda)$
-- statement:
--   For real $\lambda$, $A_6(\lambda)=2A_3-4\log 2-2\log\lambda$.

import Mathlib
import Definitions.Def_LL_S106SplitDecomp93_A3

namespace LL_S106SplitDecomp93

noncomputable section

open Real

def A6 (lam : ℝ) : ℝ := 2 * A3 - 4 * log 2 - 2 * log lam

end

end LL_S106SplitDecomp93


