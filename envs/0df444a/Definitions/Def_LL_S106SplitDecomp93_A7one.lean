-- Prove2me | Definitions.Def_LL_S106SplitDecomp93_A7one
-- name    : LL_S106SplitDecomp93_A7one
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T17:28:21.954231+00:00
-- url     : https://prove2.me/theorems/39126782-e94e-4e94-88ef-b73e7684b517
-- title:
--   The constant $A_7$ at $\lambda=1$
-- statement:
--   $\tfrac23\pi^2+4A_4-4A_3\log 2$, the value of $A_7$ at $\lambda=1$.

import Mathlib
import Definitions.Def_LL_S106SplitDecomp93_A3
import Definitions.Def_LL_S106SplitDecomp93_A4

namespace LL_S106SplitDecomp93

noncomputable section

open Real Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

def A7one : ℝ := 2 / 3 * Real.pi ^ 2 + 4 * A4 - 4 * A3 * Real.log 2

end

end LL_S106SplitDecomp93


