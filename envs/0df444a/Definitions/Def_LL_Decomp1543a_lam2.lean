-- Prove2me | Definitions.Def_LL_Decomp1543a_lam2
-- name    : LL_Decomp1543a_lam2
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:32:34.916988+00:00
-- url     : https://prove2.me/theorems/310719f7-b4cb-4544-afba-b4b7ce6cbe59
-- title:
--   Second Vaughan coefficient
-- statement:
--   For real $V$ and natural $n$, define $\Lambda_2(V,n)=\sum_{t\mid n,\ t\le V}\mu(t)\log(n/t)$, using natural-number division in the logarithm; $\mu$ is the Möbius function and the divisor sum is empty at $n=0$.

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def lam2 (V : ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ n.divisors.filter (fun t : ℕ => (t : ℝ) ≤ V), (moebius t : ℝ) * Real.log ((n / t : ℕ) : ℝ)
end LL_Decomp1543a


