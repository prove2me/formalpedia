-- Prove2me | Definitions.Def_KashUpgrade_blockValue
-- name    : KashUpgrade_blockValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:49.043439+00:00
-- url     : https://prove2.me/theorems/29da883d-5d91-405e-904d-1f1bae3568f4
-- title:
--   The first-order value of a block
-- statement:
--   The right-hand side of the first-order condition of a block $B$:
--   $$
--   \frac{c\sum_{\ell\in B}A^j_\ell}{\sum_{\ell\in B}A^j_\ell(s_\ell-s_{\ell-1})} .
--   $$
--
--   **Formalization Note** On a block whose weights all vanish this reads $0/0$, which the paper leaves undefined; Lean gives $0$. The prices of such indices enter no revenue.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (18), (20), p.17; Algorithm 1, p.19

import Mathlib

namespace KashUpgrade

/-- **The first-order value of a block.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (18)/(20), p.17 and Algorithm 1, p.19:
`c ∑_{ℓ∈B} A_ℓ / ∑_{ℓ∈B} A_ℓ (s_ℓ - s_{ℓ-1})`.

**Formalization Note** On a block whose weights all vanish this reads `0 / 0`, which the paper leaves
undefined; Lean gives `0`. The prices of such indices enter no revenue. -/
noncomputable def blockValue (c : ℝ) (s : ℕ → ℕ) (A : ℕ → ℝ) (B : Finset ℕ) : ℝ :=
  (c * ∑ ℓ ∈ B, A ℓ) / ∑ ℓ ∈ B, A ℓ * ((s ℓ : ℝ) - s (ℓ - 1))

end KashUpgrade


