-- Prove2me | Definitions.Def_KashUpgrade_ThresholdFeasible
-- name    : KashUpgrade_ThresholdFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:58.792083+00:00
-- url     : https://prove2.me/theorems/0dc18680-c5bb-43cc-b51a-0031e2d1b76c
-- title:
--   The constraints of problem (12)
-- statement:
--   A threshold vector is feasible for problem (12) if
--   $$
--   p^*=\theta^j_j\le\theta^j_{j+1}\le\dots\le\theta^j_{j+n},
--   $$
--   each threshold being a customer type, i.e. a point of the support.
--
--   **Formalization Note** The restriction to the support changes no optimal value: a threshold above a finite $\zeta$ has $1-F=0$ and the same term value as the threshold $\zeta$.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (12), p.14

import Mathlib
import Definitions.Def_KashUpgrade_typeSupport

namespace KashUpgrade

/-- **The constraints of problem (12).** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (12), p.14:
`p* = θ_j ≤ θ_{j+1} ≤ … ≤ θ_{j+n}`.

**Formalization Note** Thresholds are customer types, so they lie in the support. This changes no
optimal value: a threshold above a finite `ζ` has `1 - F = 0`, and it has the same term value as the
threshold `ζ`. -/
def ThresholdFeasible (ζ : ENNReal) (p : ℝ) (j n : ℕ) (θ : ℕ → ℝ) : Prop :=
  θ j = p ∧ (∀ i, i < n → θ (j + i) ≤ θ (j + i + 1)) ∧ ∀ i, i ≤ n → θ (j + i) ∈ typeSupport ζ

end KashUpgrade


