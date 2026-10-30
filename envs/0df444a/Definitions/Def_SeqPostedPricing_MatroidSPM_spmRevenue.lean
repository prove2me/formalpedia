-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_spmRevenue
-- name    : SeqPostedPricing_MatroidSPM_spmRevenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:38:21.493122+00:00
-- url     : https://prove2.me/theorems/72021247-a361-4eb3-9f94-52b2555ddee2
-- title:
--   Expected revenue $\mathcal R^\sigma_{\mathbf p}$ of an SPM
-- statement:
--   For independent values $v_i\sim\mu_i$, the **expected revenue** of the SPM with order $\sigma$ and prices $\mathbf p$ is
--
--   $$
--   \mathcal R^\sigma_{\mathbf p}=\mathbb E_{\mathbf v}\Big[\sum_{i\in A(\mathbf v)}p_i\Big],
--   $$
--
--   where $A(\mathbf v)$ is the set of agents served at the value profile $\mathbf v$.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, unnumbered, p. 4

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_spmServedBefore
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **Expected revenue `R^σ_p` of a sequential posted-price mechanism.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §2.2, unnumbered, p. 4 (PDF p. 6): "the expected revenue of the sequential mechanism, R^σ_p".

`spmRevenue Feas μ p active σ = E_v[Σ_{i ∈ A(v)} p_i]`, where `A(v)` is the set of agents the
SPM serves at the value profile `v` and the values are independent, `v_i ∼ μ i`.

**Formalization Note.** The integrand is a finite sum of prices times indicators of events
`{p_i ≤ v_i}`-generated, so it is bounded and integrable for probability measures `μ i`. -/
noncomputable def spmRevenue {n : ℕ} (Feas : Finset (Fin n) → Prop) (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (p : Fin n → ℝ) (active : Finset (Fin n)) (σ : Fin n ≃ Fin n) : ℝ :=
  ∫ v, ∑ i ∈ spmServedBefore Feas p active σ v n, p i ∂(Measure.pi μ)

end SeqPostedPricing.MatroidSPM


