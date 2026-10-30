-- Prove2me | Definitions.Def_LL_Decomp1543a_lRange
-- name    : LL_Decomp1543a_lRange
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:36:16.166986+00:00
-- url     : https://prove2.me/theorems/ed137948-b89f-45ef-a73a-a982885b0525
-- title:
--   Finite coefficient interval
-- statement:
--   For natural $N$ and real $U,X$, define $L(N,U,X)=\{m\in\mathbb N:1\le m\le N,\ U<m\le X\}$.

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def lRange (N : ℕ) (U X : ℝ) : Finset ℕ := (Icc 1 N).filter (fun m => U < m ∧ (m : ℝ) ≤ X)
end LL_Decomp1543a


