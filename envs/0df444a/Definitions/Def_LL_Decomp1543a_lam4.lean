-- Prove2me | Definitions.Def_LL_Decomp1543a_lam4
-- name    : LL_Decomp1543a_lam4
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:33:25.8742+00:00
-- url     : https://prove2.me/theorems/a3b2ae8c-8125-427b-977d-469fd8c9a917
-- title:
--   Fourth Vaughan coefficient
-- statement:
--   For real $U,V$ and natural $n$, define $\Lambda_4(U,V,n)=\sum_{t\mid n,\ V<t}\mu(t)a_{n/t}(U)$, using natural-number division and an empty divisor sum at $n=0$.

import Mathlib
import Definitions.Def_LL_Decomp1543a_am

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def lam4 (U V : ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ n.divisors.filter (fun t : ℕ => V < (t : ℝ)), (moebius t : ℝ) * am U (n / t)
end LL_Decomp1543a


