-- Prove2me | Definitions.Def_KashUpgrade_firstOrderThreshold
-- name    : KashUpgrade_firstOrderThreshold
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:12.629824+00:00
-- url     : https://prove2.me/theorems/789fe238-1a0c-426e-9fc8-e3d4b35cf036
-- title:
--   The first-order threshold $\theta^{j,FOC}_{\mathcal L(i)}$
-- statement:
--   The solution of the first-order condition of a block $B$:
--   $$
--   \theta^{j,FOC}_{B}:=v^{-1}\Bigl(\frac{c\sum_{\ell\in B}A^j_\ell}{\sum_{\ell\in B}A^j_\ell(s_\ell-s_{\ell-1})}\Bigr).
--   $$
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (20), p.17

import Mathlib
import Definitions.Def_KashUpgrade_virtualInverse
import Definitions.Def_KashUpgrade_blockValue

namespace KashUpgrade

/-- **The first-order threshold of a block.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (20), p.17: `θ^{FOC}_B := v⁻¹(c ∑A / ∑A Δ)`. -/
noncomputable def firstOrderThreshold (f : ℝ → ℝ) (ζ : ENNReal) (c : ℝ) (s : ℕ → ℕ) (A : ℕ → ℝ)
    (B : Finset ℕ) : ℝ :=
  (virtualInverse f ζ (blockValue c s A B)).toReal

end KashUpgrade


