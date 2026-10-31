-- Prove2me | Definitions.Def_KashUpgrade_initialGamma
-- name    : KashUpgrade_initialGamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:44.289451+00:00
-- url     : https://prove2.me/theorems/2a624383-d20b-4f17-a377-a6e1d7cec438
-- title:
--   The initial values $\gamma_i$ of OptimalLumping
-- statement:
--   The initial right-hand sides of OptimalLumping:
--   $$
--   \gamma^j_i\leftarrow\frac{c}{s_i-s_{i-1}} .
--   $$
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Algorithm 1, p.19

import Mathlib

namespace KashUpgrade

/-- **The initial right-hand sides.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Algorithm 1, p.19: `γ_i ← c / (s_i - s_{i-1})`. -/
noncomputable def initialGamma (c : ℝ) (s : ℕ → ℕ) (i : ℕ) : ℝ :=
  c / ((s i : ℝ) - s (i - 1))

end KashUpgrade


