-- Prove2me | Definitions.Def_LL_Decomp1543a_tBlock
-- name    : LL_Decomp1543a_tBlock
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:33:54.458327+00:00
-- url     : https://prove2.me/theorems/d853b886-1798-4adb-ad49-4dd333e37320
-- title:
--   Finite dyadic block
-- statement:
--   For natural $N$ and real $M$, define $T(N,M)=\{t\in\mathbb N:1\le t\le N,\ M<t\le2M\}$.

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def tBlock (N : ℕ) (M : ℝ) : Finset ℕ := (Icc 1 N).filter (fun t => M < t ∧ (t : ℝ) ≤ 2 * M)
end LL_Decomp1543a


