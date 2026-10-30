-- Prove2me | Definitions.Def_LL_Decomp1543a_block
-- name    : LL_Decomp1543a_block
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:35:50.108127+00:00
-- url     : https://prove2.me/theorems/9245912a-24dc-4108-b520-672d6b665271
-- title:
--   Möbius-weighted dyadic block sum
-- statement:
--   For real $c,U,M,\alpha$ and natural $N$, define $B(c,N,U,M,\alpha)=\sum_{t\in T(N,M)}\mu(t)I(c,N,U,\alpha,t)$.

import Mathlib
import Definitions.Def_LL_Decomp1543a_e
import Definitions.Def_LL_Decomp1543a_am
import Definitions.Def_LL_Decomp1543a_tBlock
import Definitions.Def_LL_Decomp1543a_mRange
import Definitions.Def_LL_Decomp1543a_inner

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def block (c : ℝ) (N : ℕ) (U M α : ℝ) : ℂ :=
  ∑ t ∈ tBlock N M, (moebius t : ℂ) * inner c N U α t
end LL_Decomp1543a


