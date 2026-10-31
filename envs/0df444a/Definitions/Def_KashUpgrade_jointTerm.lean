-- Prove2me | Definitions.Def_KashUpgrade_jointTerm
-- name    : KashUpgrade_jointTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:54.059515+00:00
-- url     : https://prove2.me/theorems/a8691360-8af7-492e-8a3a-0eff4ecf1ea5
-- title:
--   The joint term of a block
-- statement:
--   The joint term of a block $B$ in the objective of problem (12), when all thresholds of the block equal $\theta$:
--   $$
--   (1-F(\theta))\sum_{\ell\in B}A^j_\ell\bigl((s_\ell-s_{\ell-1})\theta-c\bigr).
--   $$
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (39), p.51

import Mathlib
import Definitions.Def_KashUpgrade_typeCdf

namespace KashUpgrade

/-- **The joint term of a block.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (39), p.51:
`(1 - F θ) ∑_{ℓ∈B} A_ℓ ((s_ℓ - s_{ℓ-1}) θ - c)`. -/
noncomputable def jointTerm (f : ℝ → ℝ) (c : ℝ) (s : ℕ → ℕ) (A : ℕ → ℝ) (B : Finset ℕ)
    (θ : ℝ) : ℝ :=
  (1 - typeCdf f θ) * ∑ ℓ ∈ B, A ℓ * (((s ℓ : ℝ) - s (ℓ - 1)) * θ - c)

end KashUpgrade


