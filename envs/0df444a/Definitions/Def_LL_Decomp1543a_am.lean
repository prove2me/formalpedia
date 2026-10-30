-- Prove2me | Definitions.Def_LL_Decomp1543a_am
-- name    : LL_Decomp1543a_am
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:32:58.397918+00:00
-- url     : https://prove2.me/theorems/835b2e67-a830-4918-aea7-a1dac0ae6a64
-- title:
--   Large-divisor von Mangoldt weight
-- statement:
--   For real $U$ and natural $m$, define $a_m(U)=\sum_{r\mid m,\ U<r}\Lambda(r)$, with an empty divisor sum at $m=0$.

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def am (U : ℝ) (m : ℕ) : ℝ :=
  ∑ r ∈ m.divisors.filter (fun r : ℕ => U < (r : ℝ)), vonMangoldt r
end LL_Decomp1543a


