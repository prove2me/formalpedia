-- Prove2me | Definitions.Def_LL_Decomp1543c_rangeN
-- name    : LL_Decomp1543c_rangeN
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T17:28:12.36003+00:00
-- url     : https://prove2.me/theorems/80d37add-9ee3-4df3-a74a-9a6d47c21589
-- title:
--   The summation range
-- statement:
--   For real $c$ and natural $N$, the finite set $\{n\in\mathbb N:1\le n\le N,\ cN<n\}$.

import Mathlib

namespace LL_Decomp1543c

open Real Finset ArithmeticFunction

noncomputable def rangeN (c : ℝ) (N : ℕ) : Finset ℕ := (Icc 1 N).filter (fun n => c * N < n)

end LL_Decomp1543c


