-- Prove2me | Definitions.Def_LL_Decomp1543a_rangeN
-- name    : LL_Decomp1543a_rangeN
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:31:41.708683+00:00
-- url     : https://prove2.me/theorems/83363195-c76f-45aa-a3b9-f779a40cd880
-- title:
--   Truncated natural interval
-- statement:
--   For real $c$ and natural $N$, define $R(c,N)=\{n\in\mathbb N:1\le n\le N,\ cN<n\}$.

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def rangeN (c : ℝ) (N : ℕ) : Finset ℕ := (Icc 1 N).filter (fun n => c * N < n)
end LL_Decomp1543a


