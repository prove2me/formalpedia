-- Prove2me | Definitions.Def_LL_S106SplitDecomp93_A4
-- name    : LL_S106SplitDecomp93_A4
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T17:15:38.125621+00:00
-- url     : https://prove2.me/theorems/dd07fd4f-53ec-4842-a98d-ef5918ee6178
-- title:
--   The constant $A_4$ of the second order term
-- statement:
--   $A_4=\tfrac14A_3^2-2\gamma^2-4\gamma_1+\tfrac14\log^2 2-A_2$, where $\gamma_1$ is the first Stieltjes constant as defined in this mission.

import Mathlib
import Definitions.Def_LL_S106SplitDecomp93_stieltjes1
import Definitions.Def_LL_S106SplitDecomp93_A2
import Definitions.Def_LL_S106SplitDecomp93_A3

namespace LL_S106SplitDecomp93

noncomputable section

open Finset Real

def A4 : ℝ := A3 ^ 2 / 4 - 2 * eulerMascheroniConstant ^ 2 -
  4 * stieltjes1 + Real.log 2 ^ 2 / 4 - A2

end

end LL_S106SplitDecomp93


