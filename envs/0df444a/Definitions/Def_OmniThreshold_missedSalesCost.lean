-- Prove2me | Definitions.Def_OmniThreshold_missedSalesCost
-- name    : OmniThreshold_missedSalesCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:59.568283+00:00
-- url     : https://prove2.me/theorems/9c96261c-ab93-49bc-b166-18b4028311a0
-- title:
--   Expected missed-sales cost $P(S,D)$
-- statement:
--   For a Global Threshold $S$ and a law $\mu$ of the demands, the **expected missed-sales cost** is
--   $$
--   P(S,\mu)=\mathbb E_\mu\Bigl[p\,\min\Bigl(L-\min\Bigl(S,\sum_{i}\mathcal D_i^O,L\Bigr),\ \sum_i(\mathcal D_i^O-A_i^O(S))\Bigr)\Bigr],\qquad L=\sum_i\bigl(\mathcal I_i-\min(\mathcal I_i,\mathcal D_i^P)\bigr).
--   $$
--   Here $L$ is the inventory left after in-store demand. By the first observation of the proof of Theorem 2, $\min(S,\sum_i\mathcal D_i^O,L)$ is the number of online orders filled at an optimum. This is the paper's $P(S,D)$, the "missed sales" component of the cost.
--
--   **Formalization Note** The three-term minimum is written as $\min(\min(S,\sum_i\mathcal D_i^O),L)$. All quantities are cast to $\mathbb R$.
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, proof of Theorem 2, p.9

import Mathlib
import Definitions.Def_OmniThreshold_onlineDemand
import Definitions.Def_OmniThreshold_acceptedCount

namespace OmniThreshold

open MeasureTheory

/-- The **expected missed-sales cost under the Global Threshold `S` and the demand law `μ`**, the
paper's `P(S, D)` (Jia, Karp, Ravi & Tayur, *Effective Online Order Acceptance Policies for
Omni-Channel Fulfillment*, SSRN 3932692, proof of Theorem 2, p.9):
```
P(S, D) = E_D[ p · min( ∑_i (I_i − min(I_i, D_i^P)) − min(S, ∑_i D_i^O, ∑_i (I_i − min(I_i, D_i^P))),
                        ∑_i (D_i^O − A_i^O) ) ].
```

**Formalization Note** `D^O = onlineDemand X N`, `A^O = acceptedCount X N S`, the law `D` is the
measure `μ`, and all quantities are cast to `ℝ`. The three-term `min` is written
`min (min S (∑ D^O)) (∑ (I − min(I, D^P)))`. The first inner term of the formula on p.9 is printed
`min(I_i − D_i^P)`, a misprint for `min(I_i, D_i^P)`, which is what the same formula and LP (1) have
elsewhere and what is written here. -/
noncomputable def missedSalesCost {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (p : ℝ)
    (I : Fin n → ℕ) (X : ℕ → Ω → Fin n) (N : Ω → ℕ) (DP : Ω → Fin n → ℕ) (μ : Measure Ω)
    (S : ℕ) : ℝ :=
  ∫ ω, p * min
      ((∑ i, ((I i : ℝ) - min (I i : ℝ) (DP ω i : ℝ))) -
        min (min (S : ℝ) (∑ i, (onlineDemand X N ω i : ℝ)))
          (∑ i, ((I i : ℝ) - min (I i : ℝ) (DP ω i : ℝ))))
      (∑ i, ((onlineDemand X N ω i : ℝ) - (acceptedCount X N S ω i : ℝ))) ∂μ

end OmniThreshold


