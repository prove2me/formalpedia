-- Prove2me | Definitions.Def_GradedReserve_Supplement_expRevenue
-- name    : GradedReserve_Supplement_expRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:37:51.107887+00:00
-- url     : https://prove2.me/theorems/4d5c5b1d-a0b4-4729-8463-2839b5da3cbf
-- title:
--   Expected revenue $\sum_i E[m_i(V_i)]$ of a strategy profile
-- statement:
--   The seller's expected revenue under a strategy profile $\sigma$ is
--   $$\mathrm{Rev}(\sigma)=\sum_{i=1}^n \mathbb E\big[m_i(V_i)\big].$$
--   For the truthful profile $\sigma_j(v)=\delta_v$ it is the anchored revenue.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Definition 2.1, p.4 (PDF 5); Theorems 3.4 and 4.3, pp.7, 9 (PDF 8, 10)

import Mathlib
import Definitions.Def_GradedReserve_typeMeasure
import Definitions.Def_GradedReserve_Supplement_interimM
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The seller's expected revenue under the strategy profile `σ`: the sum over bidders of the
expected interim payment, `Σᵢ E[mᵢ(Vᵢ)]` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Definition 2.1, p.4, PDF 5, "expected revenue";
Theorem 3.4, p.7, PDF 8, and Theorem 4.3, p.9, PDF 10). With `σ` the truthful profile
(`σ j v = δ_v`) it is the anchored revenue. -/
noncomputable def expRevenue {n : ℕ} (M : Mechanism n) (f : ℝ → ℝ) (σ : Fin n → Kernel ℝ ℝ) :
    ℝ :=
  ∑ i, ∫ v, interimM M f σ i v ∂(typeMeasure f)

end GradedReserve.Supplement


