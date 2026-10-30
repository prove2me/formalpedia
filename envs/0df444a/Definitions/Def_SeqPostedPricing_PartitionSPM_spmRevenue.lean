-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_spmRevenue
-- name    : SeqPostedPricing_PartitionSPM_spmRevenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:10:44.962323+00:00
-- url     : https://prove2.me/theorems/45b78dcf-56ee-488a-903e-865c8a9a34a4
-- title:
--   Expected revenue $R^\sigma_p$ of an SPM
-- statement:
--   For independent values $v_i \sim \mu_i$, the **expected revenue** of the SPM with prices $p$, active agents and order $\sigma$ is
--
--   $$
--   R^\sigma_p = \mathbb E\Big[\sum_{i \in A} p_i\Big],
--   $$
--
--   where $A$ is the set of agents the SPM finally serves.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_spmServedBefore

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory in
/-- **Expected revenue of an SPM** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, p. 4 = PDF p. 6: "the expected revenue of the
sequential mechanism, R^σ_p"). Every served agent `i` pays its posted price `p i`; the revenue is the
expectation of `Σ_{i ∈ A} p_i` under the product law of the values.

**Formalization Note** The integrand is a finite sum of prices times indicators of measurable events
(it depends on `v` only through the comparisons `p i ≤ v i`), so it is bounded and integrable. -/
noncomputable def spmRevenue {n : ℕ} (Feas : Finset (Fin n) → Prop) (μ : Fin n → Measure ℝ)
    (p : Fin n → ℝ) (active : Finset (Fin n)) (σ : Fin n ≃ Fin n) : ℝ :=
  ∫ v, ∑ i ∈ spmServedBefore Feas p active σ v n, p i ∂(Measure.pi μ)

end SeqPostedPricing.PartitionSPM


