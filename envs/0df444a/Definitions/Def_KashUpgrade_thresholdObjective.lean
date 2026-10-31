-- Prove2me | Definitions.Def_KashUpgrade_thresholdObjective
-- name    : KashUpgrade_thresholdObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:57.782651+00:00
-- url     : https://prove2.me/theorems/fbff02dc-1b9e-4d85-9ccd-88e36619a44e
-- title:
--   The objective of problem (12)
-- statement:
--   The objective of the threshold problem of slice $j$:
--   $$
--   A^j_j\bigl(1-F(\theta^j_j)\bigr)s_j\theta^j_j+\sum_{i=1}^{n}A^j_{j+i}\bigl(1-F(\theta^j_{j+i})\bigr)\bigl((s_{j+i}-s_{j+i-1})\theta^j_{j+i}-c\bigr).
--   $$
--
--   **Formalization Note** Weights and thresholds are functions of the absolute class index, and the weights are an arbitrary function here. The definition is used with the weights of (37)–(38), and with arbitrary weights in Lemmas 2 and 3.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (12), p.14

import Mathlib
import Definitions.Def_KashUpgrade_typeCdf

namespace KashUpgrade

/-- **The objective of problem (12).** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (12), p.14:
`A_j (1 - F θ_j) s_j θ_j + ∑_{i=1}^n A_{j+i} (1 - F θ_{j+i}) ((s_{j+i} - s_{j+i-1}) θ_{j+i} - c)`.
Thresholds and weights are indexed by the absolute class index. -/
noncomputable def thresholdObjective (f : ℝ → ℝ) (c : ℝ) (s : ℕ → ℕ) (A : ℕ → ℝ) (j n : ℕ)
    (θ : ℕ → ℝ) : ℝ :=
  A j * (1 - typeCdf f (θ j)) * s j * θ j +
    ∑ i ∈ Finset.Icc 1 n,
      A (j + i) * (1 - typeCdf f (θ (j + i))) *
        (((s (j + i) : ℝ) - s (j + i - 1)) * θ (j + i) - c)

end KashUpgrade


