-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_revenue
-- name    : SeqPostedPricing_MatroidSPM_revenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:32:12.932105+00:00
-- url     : https://prove2.me/theorems/51319093-0544-4e1f-97f8-f5312ff74112
-- title:
--   Expected revenue $\mathcal R^M=\mathbb E_{\mathbf v}\big[\sum_i\pi_i(\mathbf v)\big]$
-- statement:
--   The values $v_1,\dots,v_n$ are independent, $v_i\sim\mu_i$. The **expected revenue** of a mechanism $M$ is
--
--   $$
--   \mathcal R^M=\mathbb E_{\mathbf v\sim\mu_1\otimes\dots\otimes\mu_n}\Big[\sum_{i=1}^n\pi_i(\mathbf v)\Big].
--   $$
--
--   **Formalization Note** This is a Bochner integral over the product measure; Lean assigns $0$ to a non-integrable integrand, so every statement uses it only for mechanisms whose payments are integrable (`IsAdmissible`).
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.1, p. 4; App. A, p. 12

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_Mechanism
open MeasureTheory

namespace SeqPostedPricing.MatroidSPM

/-- **Expected revenue `R^M` of a mechanism.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §2.1, p. 4 (PDF p. 6) (values independent with distributions `F_i`) and App. A, p. 12
(PDF p. 14) (`R^M`).

`revenue μ M = E_v[Σ_i π_i(v)]`, the expectation over independent values `v_i ∼ μ i` (the joint
law is the product measure `Measure.pi μ`).

**Formalization Note.** This is a Bochner integral, which Lean sets to `0` for a non-integrable
integrand; every statement of the mission uses it only for mechanisms with integrable payments
(`IsAdmissible`). -/
noncomputable def revenue {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (M : Mechanism n) : ℝ :=
  ∫ v, ∑ i, M.pay v i ∂(Measure.pi μ)

end SeqPostedPricing.MatroidSPM


