-- Prove2me | Definitions.Def_LL_S106SplitDecomp93_A7
-- name    : LL_S106SplitDecomp93_A7
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T17:55:02.269331+00:00
-- url     : https://prove2.me/theorems/243fed09-350f-4aa7-ab80-e6b1322f1690
-- title:
--   The scaled constant $A_7(\lambda)$
-- statement:
--   For real $\lambda$, $A_7(\lambda)=\tfrac23\pi^2+4A_4-4A_3\log2+\log^2\lambda-(2A_3-4\log 2)\log\lambda$.

import Mathlib
import Definitions.Def_LL_S106SplitDecomp93_A3
import Definitions.Def_LL_S106SplitDecomp93_A7one

namespace LL_S106SplitDecomp93

noncomputable section

open Real

def A7 (lam : ℝ) : ℝ := A7one + log lam ^ 2 - (2 * A3 - 4 * log 2) * log lam

end

end LL_S106SplitDecomp93


