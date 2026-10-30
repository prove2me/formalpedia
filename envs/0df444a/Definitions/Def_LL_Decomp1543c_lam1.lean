-- Prove2me | Definitions.Def_LL_Decomp1543c_lam1
-- name    : LL_Decomp1543c_lam1
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T17:28:57.240108+00:00
-- url     : https://prove2.me/theorems/6fe62aea-377f-4b7c-99ef-d8cdb238b025
-- title:
--   The first Vaughan coefficient
-- statement:
--   For real $U$ and natural $n$, $\Lambda_1(U,n)=\Lambda(n)$ if $n\le U$ and $0$ otherwise.

import Mathlib

namespace LL_Decomp1543c

open Real Finset ArithmeticFunction

noncomputable def lam1 (U : ℝ) (n : ℕ) : ℝ := if (n : ℝ) ≤ U then vonMangoldt n else 0

end LL_Decomp1543c


