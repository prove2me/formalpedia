-- Prove2me | Definitions.Def_LL_Decomp1543a_mRange
-- name    : LL_Decomp1543a_mRange
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:34:08.832416+00:00
-- url     : https://prove2.me/theorems/f8ca5ec2-4c4d-4b58-8ffe-46185e08999a
-- title:
--   Inner product-constrained interval
-- statement:
--   For real $c,U$ and natural $N,t$, define $\mathcal M(c,N,U,t)=\{m\in\mathbb N:1\le m\le N,\ cN<mt\le N,\ U<m\}$.

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def mRange (c : ℝ) (N : ℕ) (U : ℝ) (t : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun m => c * N < ((m * t : ℕ) : ℝ) ∧ m * t ≤ N ∧ U < m)
end LL_Decomp1543a


