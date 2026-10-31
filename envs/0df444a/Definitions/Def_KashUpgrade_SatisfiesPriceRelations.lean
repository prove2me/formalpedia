-- Prove2me | Definitions.Def_KashUpgrade_SatisfiesPriceRelations
-- name    : KashUpgrade_SatisfiesPriceRelations
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:28.734278+00:00
-- url     : https://prove2.me/theorems/b980da2a-01fd-4162-bb28-33effc1290b0
-- title:
--   The price relations (13)
-- statement:
--   A price function $x$ is related to the thresholds $\theta$ by (13) if
--   $$
--   x_{i,0}=s_ip^*,\quad 1\le i\le j;\qquad
--   x_{j+i,i}=x_{j+i-1,i-1}+(s_{j+i}-s_{j+i-1})\theta^j_{j+i}-c,\quad 1\le i\le n .
--   $$
--   With these prices a customer whose type is exactly the threshold is indifferent about upgrading.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (13), p.14

import Mathlib

namespace KashUpgrade

/-- **The price relations (13).** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (13), p.14: `x_{i,0} = s_i p*` for `1 ≤ i ≤ j`, and
`x_{j+i,i} = x_{j+i-1,i-1} + (s_{j+i} - s_{j+i-1}) θ_{j+i} - c` for `1 ≤ i ≤ n`. -/
def SatisfiesPriceRelations (s : ℕ → ℕ) (p c : ℝ) (j n : ℕ) (θ : ℕ → ℝ) (x : ℕ → ℕ → ℝ) : Prop :=
  (∀ i, 1 ≤ i → i ≤ j → x i 0 = s i * p) ∧
    ∀ i, 1 ≤ i → i ≤ n →
      x (j + i) i = x (j + i - 1) (i - 1) + ((s (j + i) : ℝ) - s (j + i - 1)) * θ (j + i) - c

end KashUpgrade


