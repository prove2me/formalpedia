-- Prove2me | Definitions.Def_LL_Decomp1543a_lam1
-- name    : LL_Decomp1543a_lam1
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:32:21.601599+00:00
-- url     : https://prove2.me/theorems/2c41a736-0b6e-4ab1-afe8-be6b1c34bb27
-- title:
--   First Vaughan coefficient
-- statement:
--   For real $U$ and natural $n$, define $\Lambda_1(U,n)=\Lambda(n)$ if $n\le U$, and zero otherwise, where $\Lambda$ is the von Mangoldt function.

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def lam1 (U : ℝ) (n : ℕ) : ℝ := if (n : ℝ) ≤ U then vonMangoldt n else 0
end LL_Decomp1543a


