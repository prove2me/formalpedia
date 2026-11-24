-- Prove2me | Definitions.Def_LL_S106SplitDecomp93_A1
-- name    : LL_S106SplitDecomp93_A1
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T16:14:28.478305+00:00
-- url     : https://prove2.me/theorems/b3320598-36b9-41c1-b8c9-c64fb2e8980f
-- title:
--   The constant $A_1=\tfrac12\log2+2A_0$
-- statement:
--   $A_1=\tfrac12\log 2+2A_0$.

import Mathlib
import Definitions.Def_LL_S106SplitDecomp93_A0

namespace LL_S106SplitDecomp93

noncomputable section

open Finset Real

def A1 : ℝ := Real.log 2 / 2 + 2 * A0

end

end LL_S106SplitDecomp93


