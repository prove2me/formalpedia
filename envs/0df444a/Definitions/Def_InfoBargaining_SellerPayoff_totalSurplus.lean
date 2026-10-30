-- Prove2me | Definitions.Def_InfoBargaining_SellerPayoff_totalSurplus
-- name    : InfoBargaining_SellerPayoff_totalSurplus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:13:14.190422+00:00
-- url     : https://prove2.me/theorems/fa76b0ff-9555-4954-8bf2-ef8d05101819
-- title:
--   Total ex ante surplus $A(\alpha,c)$
-- statement:
--   With $G(\cdot,\alpha)$ the law of the buyer's posterior mean (see `postMeanLaw`), the **total ex ante surplus** of display (7) is
--
--   $$
--   A(\alpha,c)=\int_c^{\bar v}(v-c)\,dG(v,\alpha)=\int\max\{v-c,0\}\,dG(v,\alpha).
--   $$
--
--   It is the expected gain from trade when trade happens exactly when the posterior mean exceeds the cost, gross of the information cost.
--
--   **Formalization Note** Written as the integral of $(v-c)^+$ against the posterior-mean law; a Bochner integral, which is $0$ for a non-integrable integrand, but every prior in this mission has a finite mean.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §3.1, display (7), p. 11

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_postMeanLaw

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **The total ex ante surplus `A(α, c)`, display (7).**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022),
§3.1, (7), p. 11: "A(α, c) = ∫_c^v̄ (v − c) dG(v, α)".

`totalSurplus μ α c = ∫ max(v − c, 0) dG(v, α)`, the integral taken against the law of the
posterior mean (`postMeanLaw μ α`).

**Formalization Note.** `∫_c^v̄ (v − c) dG` is written `∫ (v − c)⁺ dG`, which is the same
quantity. A Bochner integral: `0` if the integrand is not integrable; every prior used in this
mission has a finite mean, which makes it integrable. -/
noncomputable def totalSurplus (μ : Measure ℝ) (α c : ℝ) : ℝ :=
  ∫ v, max (v - c) 0 ∂(postMeanLaw μ α)

end InfoBargaining.SellerPayoff


