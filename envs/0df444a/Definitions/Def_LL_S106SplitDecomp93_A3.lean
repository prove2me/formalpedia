-- Prove2me | Definitions.Def_LL_S106SplitDecomp93_A3
-- name    : LL_S106SplitDecomp93_A3
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T17:00:00.539889+00:00
-- url     : https://prove2.me/theorems/d0270033-0541-452d-9325-c88a4c869406
-- title:
--   The constant $A_3=4\gamma+2A_1$
-- statement:
--   $A_3=4\gamma+2A_1$ with $\gamma$ the Euler Mascheroni constant; numerically $A_3=6.0234762835\ldots$.

import Mathlib
import Definitions.Def_LL_S106SplitDecomp93_A1

namespace LL_S106SplitDecomp93

noncomputable section

open Finset Real

def A3 : ℝ := 4 * eulerMascheroniConstant + 2 * A1

end

end LL_S106SplitDecomp93


