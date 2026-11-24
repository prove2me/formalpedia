-- Prove2me | Definitions.Def_LL_Decomp119LeavesIIS124CaseBRatio_V
-- name    : LL_Decomp119LeavesIIS124CaseBRatio_V
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:19:31.489905+00:00
-- url     : https://prove2.me/theorems/2538d52e-7646-418e-92b6-cfabd5bc3e11
-- title:
--   The parameter $V=x^{1/3}/3$
-- statement:
--   For real $x$, $V(x)=x^{1/3}/3$, with the real power $x^{1/3}$.

import Mathlib

namespace LL_Decomp119LeavesIIS124CaseBRatio

noncomputable section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable def V (x : ℝ) : ℝ := x ^ ((1 : ℝ) / 3) / 3

end

end LL_Decomp119LeavesIIS124CaseBRatio


