-- Prove2me | Definitions.Def_LL_Decomp1543c_nint
-- name    : LL_Decomp1543c_nint
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T17:27:33.28227+00:00
-- url     : https://prove2.me/theorems/0088a689-9d1b-4264-ad55-a8e4c5d08af9
-- title:
--   Distance to the nearest integer
-- statement:
--   For real $x$, $\|x\|=|x-\operatorname{round}(x)|$, the distance from $x$ to the nearest integer.

import Mathlib

namespace LL_Decomp1543c

open Real Finset ArithmeticFunction

noncomputable def nint (x : ℝ) : ℝ := |x - round x|

end LL_Decomp1543c


