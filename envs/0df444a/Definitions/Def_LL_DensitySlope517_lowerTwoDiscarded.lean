-- Prove2me | Definitions.Def_LL_DensitySlope517_lowerTwoDiscarded
-- name    : LL_DensitySlope517_lowerTwoDiscarded
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-17T15:36:29.192185+00:00
-- url     : https://prove2.me/theorems/9c054d5f-62e5-4c41-bd9a-deb7bb3d1838
-- title:
--   The polygon E2 of page 51
-- statement:
--   For reals $\varepsilon,a,b$, with $\theta=2(1/16-10^{-5})$ and $c_1=(1+7\theta)/15-\varepsilon$, the proposition that $c_1\le b$, $b\le a$, $a\le1/2$ and $a+2b\le1$, and that none of the following holds: $a+2b\le 1/2+(1+22\theta)/60-2\varepsilon$; or $4a+7b\le 2+\theta-\varepsilon$ together with $1/2-(\theta+3c_1)/4+\varepsilon\le a+b$; or $b\le(36\theta-2)/11-\varepsilon$ together with $4a+5b\le2+\theta-\varepsilon$ and $1/2-(\theta+c_1)/4+\varepsilon\le a+b$; or the pair $(\varepsilon,a,b)$ satisfies the region $P_1\cup P_2\cup R$ defined above with $m=a$, $n=b$. This is the polygon $E_2$ of page 51.

import Mathlib
import Definitions.Def_LL_DensitySlope517_upperPairRegion

namespace LL_DensitySlope517

def lowerTwoDiscarded (ε a b : ℝ) : Prop :=
  (1+7*(2*(1/16-1/10^5)))/15-ε ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ a+2*b ≤ 1 ∧
    ¬(a+2*b ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε ∨
      (4*a+7*b ≤ 2+2*(1/16-1/10^5)-ε ∧
        1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ a+b) ∨
      (b ≤ (36*(2*(1/16-1/10^5))-2)/11-ε ∧ 4*a+5*b ≤ 2+2*(1/16-1/10^5)-ε ∧
        1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ a+b) ∨
      upperPairRegion ε a b)

end LL_DensitySlope517


