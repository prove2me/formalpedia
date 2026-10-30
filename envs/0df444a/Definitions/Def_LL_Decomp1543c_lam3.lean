-- Prove2me | Definitions.Def_LL_Decomp1543c_lam3
-- name    : LL_Decomp1543c_lam3
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T17:29:25.197986+00:00
-- url     : https://prove2.me/theorems/daaec927-5b19-4302-8a82-d71a85da198b
-- title:
--   The third Vaughan coefficient
-- statement:
--   For real $U,V$ and natural $n$, $\Lambda_3(U,V,n)=-\sum_{r\mid n}\sum_{t\mid n}\Lambda(r)\mu(t)$, the sum over pairs with $r\le U$, $t\le V$ and $rt\mid n$.

import Mathlib

namespace LL_Decomp1543c

open Real Finset ArithmeticFunction

noncomputable def lam3 (U V : ℝ) (n : ℕ) : ℝ :=
  -∑ r ∈ n.divisors, ∑ t ∈ n.divisors,
    if (r : ℝ) ≤ U ∧ (t : ℝ) ≤ V ∧ r * t ∣ n then vonMangoldt r * (moebius t : ℝ) else 0

end LL_Decomp1543c


