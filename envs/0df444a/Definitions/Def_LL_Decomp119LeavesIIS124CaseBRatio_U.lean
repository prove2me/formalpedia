-- Prove2me | Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_U
-- name    : LL_Decomp119LeavesIIS124CaseBRatio_U
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:04:09.039597+00:00
-- url     : https://prove2.me/theorems/9ff42873-df52-470b-970b-defc8838209b
-- title:
--   The parameter $U=500\sqrt6\,x^{1/3}$
-- statement:
--   For real $x$, $U(x)=500\sqrt6\,x^{1/3}$, with the real power $x^{1/3}$.

import Mathlib

namespace LL_Decomp119LeavesIIS124CaseBRatio

noncomputable section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable def U (x : ℝ) : ℝ := 500 * Real.sqrt 6 * x ^ ((1 : ℝ) / 3)

end

end LL_Decomp119LeavesIIS124CaseBRatio


