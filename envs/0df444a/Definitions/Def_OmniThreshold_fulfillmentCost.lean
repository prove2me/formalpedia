-- Prove2me | Definitions.Def_OmniThreshold_fulfillmentCost
-- name    : OmniThreshold_fulfillmentCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:49.568255+00:00
-- url     : https://prove2.me/theorems/ccf3565f-73cf-4c81-bafc-fa446d4d2be8
-- title:
--   Expected fulfillment cost $F(S,D)$
-- statement:
--   For a Global Threshold $S$ and a law $\mu$ of the demands, the **expected fulfillment cost** is
--   $$
--   F(S,\mu)=\mathbb E_\mu\bigl[V_2(\mathcal I,\mathcal D^P,A^O(S))\bigr],
--   $$
--   the expected optimal value of LP (2) when the first $S$ orders are accepted. This is the paper's $F(S,D)$, the fulfillment component of the cost.
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, proof of Theorem 2, p.9

import Mathlib
import Definitions.Def_OmniThreshold_lp2Value
import Definitions.Def_OmniThreshold_acceptedCount

namespace OmniThreshold

open MeasureTheory

/-- The **expected fulfillment cost under the Global Threshold `S` and the demand law `μ`**, the
paper's `F(S, D)` (Jia, Karp, Ravi & Tayur, *Effective Online Order Acceptance Policies for
Omni-Channel Fulfillment*, SSRN 3932692, proof of Theorem 2, p.9: "`F(S, D)` represents the
fulfillment cost component of the model"): the expectation under `μ` of the optimal value of
LP (2) with the accepted orders `A^O_S`,
```
F(S, D) = ∫ lp2Value(I, D^P(ω), A^O_S(ω)) dμ(ω).
```

**Formalization Note** `A^O_S = acceptedCount X N S`; the law `D` is the measure `μ`. -/
noncomputable def fulfillmentCost {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (c : Fin n → ℝ)
    (s : Fin n → Fin n → ℝ) (I : Fin n → ℕ) (X : ℕ → Ω → Fin n) (N : Ω → ℕ)
    (DP : Ω → Fin n → ℕ) (μ : Measure Ω) (S : ℕ) : ℝ :=
  ∫ ω, lp2Value c s I (DP ω) (acceptedCount X N S ω) ∂μ

end OmniThreshold


