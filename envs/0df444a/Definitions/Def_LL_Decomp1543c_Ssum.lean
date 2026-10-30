-- Prove2me | Definitions.Def_LL_Decomp1543c_Ssum
-- name    : LL_Decomp1543c_Ssum
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T17:28:43.701189+00:00
-- url     : https://prove2.me/theorems/13fb84e8-5a2f-4f5b-a01c-99dae8a1c9d9
-- title:
--   The weighted exponential sum
-- statement:
--   For $f:\mathbb N\to\mathbb R$, real $c,\alpha$ and natural $N$, $S_f(c,N,\alpha)=\sum_{1\le n\le N,\ cN<n}f(n)e(\alpha n)$.

import Mathlib
import Definitions.Def_LL_Decomp1543c_e
import Definitions.Def_LL_Decomp1543c_rangeN

namespace LL_Decomp1543c

open Real Finset ArithmeticFunction

noncomputable def Ssum (f : ℕ → ℝ) (c : ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ rangeN c N, (f n : ℂ) * e (α * n)

end LL_Decomp1543c


