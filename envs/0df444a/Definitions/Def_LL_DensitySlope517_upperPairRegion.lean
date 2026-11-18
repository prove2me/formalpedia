-- Prove2me | Definitions.Def_LL_DensitySlope517_upperPairRegion
-- name    : LL_DensitySlope517_upperPairRegion
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-17T15:35:58.469698+00:00
-- url     : https://prove2.me/theorems/d245e915-5892-4924-9098-37165ef63a51
-- title:
--   The regions R, P1 and P2 of Lemma 33
-- statement:
--   For reals $\varepsilon,m,n$, with $\theta=2(1/16-10^{-5})$, the proposition that $n\le m$, $m\le 1/2$, $(1+7\theta)/15-\varepsilon\le n$ and $n\le(36\theta-2)/11-\varepsilon$, and in addition at least one of the following holds: $2n-\theta+\varepsilon\le m\le(36\theta-2)/11-\varepsilon$; or $|4m+3n-2|\le\theta-\varepsilon$; or $|4m+n-2|\le\theta-\varepsilon$. These are the regions $R$, $P_1$ and $P_2$ of Lemma 33.

import Mathlib

namespace LL_DensitySlope517

def upperPairRegion (ε m n : ℝ) : Prop :=
  n ≤ m ∧ m ≤ 1/2 ∧ (1+7*(2*(1/16-1/10^5)))/15-ε ≤ n ∧
    n ≤ (36*(2*(1/16-1/10^5))-2)/11-ε ∧
    ((2*n-(2*(1/16-1/10^5))+ε ≤ m ∧
        m ≤ (36*(2*(1/16-1/10^5))-2)/11-ε) ∨
      |4*m+3*n-2| ≤ 2*(1/16-1/10^5)-ε ∨
      |4*m+n-2| ≤ 2*(1/16-1/10^5)-ε)

end LL_DensitySlope517


