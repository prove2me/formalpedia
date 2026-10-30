-- Prove2me | Definitions.Def_LL_Decomp1543a_Jn
-- name    : LL_Decomp1543a_Jn
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:36:01.833134+00:00
-- url     : https://prove2.me/theorems/5ef28745-8f7d-4cfa-8ebb-b125d9250ddb
-- title:
--   Number of dyadic blocks
-- statement:
--   For natural $N$ and real $U,V$, define $J(N,U,V)=\lfloor\log(N/(UV))/\log2\rfloor_++1$, where $\lfloor x\rfloor_+$ is the natural-number floor, truncated at zero.

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def Jn (N : ℕ) (U V : ℝ) : ℕ := ⌊Real.log (N / (U * V)) / Real.log 2⌋₊ + 1
end LL_Decomp1543a


