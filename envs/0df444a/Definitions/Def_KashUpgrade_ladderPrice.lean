-- Prove2me | Definitions.Def_KashUpgrade_ladderPrice
-- name    : KashUpgrade_ladderPrice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:23.651377+00:00
-- url     : https://prove2.me/theorems/ebbe8dca-4dca-4a6c-9725-d8eaeb26a7ab
-- title:
--   The prices of slice $j$ in DiscriminatoryPricing
-- statement:
--   The prices set in the $j$-th loop of DiscriminatoryPricing, given the output $\gamma$ of OptimalLumping: $x_{j,0}=s_jp^*$, and for $i=1,\dots,n$,
--   $$
--   \theta^j_{j+i}\leftarrow v^{-1}(\gamma^j_{j+i}),\qquad
--   x_{j+i,i}\leftarrow x_{j+i-1,i-1}+(s_{j+i}-s_{j+i-1})\theta^j_{j+i}-c .
--   $$
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Algorithm 2, p.20

import Mathlib
import Definitions.Def_KashUpgrade_virtualInverse

namespace KashUpgrade

/-- **The prices of slice `j` in Algorithm 2.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Algorithm 2, p.20: `x_{j,0} ← s_j p*`, then for
`i = 1, …, n`, `θ_{j+i} ← v⁻¹(γ_{j+i})` and
`x_{j+i,i} ← x_{j+i-1,i-1} + (s_{j+i} - s_{j+i-1}) θ_{j+i} - c`. Here
`ladderPrice f ζ s c p γ j i` is `x_{j+i,i}`. -/
noncomputable def ladderPrice (f : ℝ → ℝ) (ζ : ENNReal) (s : ℕ → ℕ) (c p : ℝ) (γ : ℕ → ℝ)
    (j : ℕ) : ℕ → ℝ
  | 0 => s j * p
  | i + 1 => ladderPrice f ζ s c p γ j i +
      ((s (j + i + 1) : ℝ) - s (j + i)) * (virtualInverse f ζ (γ (j + i + 1))).toReal - c

end KashUpgrade


