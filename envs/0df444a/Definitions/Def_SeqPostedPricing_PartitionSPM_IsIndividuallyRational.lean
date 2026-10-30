-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_IsIndividuallyRational
-- name    : SeqPostedPricing_PartitionSPM_IsIndividuallyRational
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:04:12.717816+00:00
-- url     : https://prove2.me/theorems/bdead71c-4dd3-4aa7-9cc9-d99e32c5f11a
-- title:
--   Individually rational mechanism
-- statement:
--   A mechanism $M$ is **individually rational** if no agent who reports truthfully gets negative utility: for almost every value profile $v$ (under the product law of the values) and every agent $i$, $u_i(v_i; v) \ge 0$.
--
--   **Formalization Note** Ex-post individual rationality for almost every true profile (types that occur with probability $0$ are not constrained).
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 3 and App. B, pp. 5, 13 (PDF pp. 7, 15)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_utility

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory in
/-- **Individual rationality** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 3 and App. B, pp. 5, 13–14 = PDF pp. 7, 15–16:
"individually rational"). Under truthful reporting no agent gets negative utility, for almost every
value profile under the product law `μ_1 × ⋯ × μ_n`.

**Formalization Note** Ex-post individual rationality for almost every true profile (types that
occur with probability `0` are not constrained). -/
def IsIndividuallyRational {n : ℕ} (μ : Fin n → Measure ℝ) (M : Mechanism n) : Prop :=
  ∀ᵐ v ∂(Measure.pi μ), ∀ i : Fin n, 0 ≤ utility M i (v i) v

end SeqPostedPricing.PartitionSPM


