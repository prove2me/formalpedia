-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_revenue
-- name    : SeqPostedPricing_PartitionSPM_revenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:04:43.212906+00:00
-- url     : https://prove2.me/theorems/fdfba7e5-e5be-4fc9-87aa-fbd17820def8
-- title:
--   Expected revenue $R^M$ of a mechanism
-- statement:
--   Let the values $v_1, \dots, v_n$ be independent with laws $\mu_1, \dots, \mu_n$. The **expected revenue** of a mechanism $M$ is
--
--   $$
--   R^M = \mathbb E_{v \sim \mu_1 \times \cdots \times \mu_n}\Big[\sum_{i=1}^n \pi_i(v)\Big].
--   $$
--
--   **Formalization Note** A Bochner integral, which is the expected revenue only when the payments are integrable; admissible mechanisms are required to have integrable payments.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, App. A, p. 12 (PDF p. 14): "Denoting the revenue of a mechanism A by R^A"; §2.1, p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_Mechanism

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory in
/-- **Expected revenue of a mechanism** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, App. A, p. 12 = PDF p. 14: "Denoting the revenue of a
mechanism A by R^A"). With independent values `v_i ∼ μ i` (§2.1, p. 4), `R^M = E[Σ_i π_i(v)]`, the
expectation under the product law `μ_1 × ⋯ × μ_n`.

**Formalization Note** A Bochner integral: it is the expected revenue only when the payments are
integrable, which `IsAdmissible` requires. -/
noncomputable def revenue {n : ℕ} (μ : Fin n → Measure ℝ) (M : Mechanism n) : ℝ :=
  ∫ v, ∑ i, M.pay v i ∂(Measure.pi μ)

end SeqPostedPricing.PartitionSPM


