-- Prove2me | Definitions.Def_LL_Decomp1543c_Vf
-- name    : LL_Decomp1543c_Vf
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T17:29:49.201256+00:00
-- url     : https://prove2.me/theorems/78395a00-1509-4273-9483-63b9c369d0c0
-- title:
--   The parameter $V$
-- statement:
--   For natural $N$, $V(N)=N^{2/5}(\log N)^{1/5}$, with real powers.

import Mathlib

namespace LL_Decomp1543c

open Real Finset ArithmeticFunction

noncomputable def Vf (N : ℕ) : ℝ := (N : ℝ) ^ ((2 : ℝ) / 5) * Real.log N ^ ((1 : ℝ) / 5)

end LL_Decomp1543c


