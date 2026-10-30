-- Prove2me | Definitions.Def_LL_Decomp1543a_lam3
-- name    : LL_Decomp1543a_lam3
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:32:46.893214+00:00
-- url     : https://prove2.me/theorems/0fa9beda-2cf9-4151-98d9-0300b54b2dce
-- title:
--   Third Vaughan coefficient
-- statement:
--   For real $U,V$ and natural $n$, define $\Lambda_3(U,V,n)=-\sum_{r\mid n}\sum_{t\mid n,\ r\le U,\ t\le V,\ rt\mid n}\Lambda(r)\mu(t)$, with empty divisor sums at $n=0$.

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def lam3 (U V : ℝ) (n : ℕ) : ℝ :=
  -∑ r ∈ n.divisors, ∑ t ∈ n.divisors,
    if (r : ℝ) ≤ U ∧ (t : ℝ) ≤ V ∧ r * t ∣ n then vonMangoldt r * (moebius t : ℝ) else 0
end LL_Decomp1543a


