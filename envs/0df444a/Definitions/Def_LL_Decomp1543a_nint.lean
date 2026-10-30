-- Prove2me | Definitions.Def_LL_Decomp1543a_nint
-- name    : LL_Decomp1543a_nint
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:30:54.188473+00:00
-- url     : https://prove2.me/theorems/a16dd29d-2dbc-49d2-9e29-a82a2ea8499f
-- title:
--   Distance to the nearest integer
-- statement:
--   For real $x$, define $\operatorname{nint}(x)=|x-\operatorname{round}(x)|$, the distance to the nearest integer.

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def nint (x : ℝ) : ℝ := |x - round x|
end LL_Decomp1543a


