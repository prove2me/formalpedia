-- Prove2me | Definitions.Def_LL_Decomp1543c_lam2
-- name    : LL_Decomp1543c_lam2
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T17:29:11.09551+00:00
-- url     : https://prove2.me/theorems/d146ba5f-f63a-4154-bee4-c55d339a445b
-- title:
--   The second Vaughan coefficient
-- statement:
--   For real $V$ and natural $n$, $\Lambda_2(V,n)=\sum_{t\mid n,\ t\le V}\mu(t)\log(n/t)$, with $n/t$ the natural quotient.

import Mathlib

namespace LL_Decomp1543c

open Real Finset ArithmeticFunction

noncomputable def lam2 (V : ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ n.divisors.filter (fun t : ℕ => (t : ℝ) ≤ V), (moebius t : ℝ) * Real.log ((n / t : ℕ) : ℝ)

end LL_Decomp1543c


