-- Prove2me | Definitions.Def_KashUpgrade_discriminatoryPrices
-- name    : KashUpgrade_discriminatoryPrices
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:28.931713+00:00
-- url     : https://prove2.me/theorems/e8bb128d-b715-4d26-9000-5ae6db32b7a8
-- title:
--   The output of DiscriminatoryPricing
-- statement:
--   The price function returned by DiscriminatoryPricing, given the output $\gamma^j$ of OptimalLumping for every $j$: the price $x_{k,m}$ is the one set in the loop of slice $j=k-m$, for $j\ge1$ and $m\le n$.
--
--   Each pair $(k,m)$ is set by exactly one slice, which is the decoupling behind the algorithm.
--
--   **Formalization Note** The algorithm sets no other price and the model never reads one. They are $0$ here.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Algorithm 2, p.20

import Mathlib
import Definitions.Def_KashUpgrade_ladderPrice

namespace KashUpgrade

/-- **The output of DiscriminatoryPricing.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Algorithm 2, p.20: given the output `γ^j` of
OptimalLumping for every `j`, the price of class `k` at experience `m` is the one set in the loop of
slice `j = k - m`, for `1 ≤ j` and `m ≤ n`. Each pair `(k, m)` is set by exactly one slice. The
algorithm sets no other price and the model never reads one, so they are `0` here. -/
noncomputable def discriminatoryPrices (f : ℝ → ℝ) (ζ : ENNReal) (s : ℕ → ℕ) (c p : ℝ) (n : ℕ)
    (γ : ℕ → ℕ → ℝ) (k m : ℕ) : ℝ :=
  if m < k ∧ m ≤ n then ladderPrice f ζ s c p (γ (k - m)) (k - m) m else 0

end KashUpgrade


