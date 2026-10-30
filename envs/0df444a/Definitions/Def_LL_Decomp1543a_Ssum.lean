-- Prove2me | Definitions.Def_LL_Decomp1543a_Ssum
-- name    : LL_Decomp1543a_Ssum
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:32:07.141276+00:00
-- url     : https://prove2.me/theorems/682b8ed6-54f9-41c7-a80d-8b35311234ac
-- title:
--   Weighted exponential sum
-- statement:
--   For $f:\mathbb N\to\mathbb R$, real $c,\alpha$ and natural $N$, define $S_f(c,N,\alpha)=\sum_{n\in R(c,N)}f(n)e(\alpha n)$.

import Mathlib
import Definitions.Def_LL_Decomp1543a_e
import Definitions.Def_LL_Decomp1543a_rangeN

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def Ssum (f : ℕ → ℝ) (c : ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ rangeN c N, (f n : ℂ) * e (α * n)
end LL_Decomp1543a


