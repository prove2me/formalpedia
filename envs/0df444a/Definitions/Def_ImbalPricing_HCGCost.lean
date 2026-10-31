-- Prove2me | Definitions.Def_ImbalPricing_HCGCost
-- name    : ImbalPricing_HCGCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:45.871801+00:00
-- url     : https://prove2.me/theorems/e459dd31-5104-4dac-aac5-4a5ee34dad57
-- title:
--   Cost $C(H_1,H_2)$ of the high-cost generator (3) and deadweight loss (4)
-- statement:
--   A nonstrategic high-cost generator (HCG) schedules a production $H_1$ in Stage 1 (day ahead) and adjusts it by $H_2$ in Stage 2 (delivery); $H_2$ may be negative. Write $\mathcal H=H_1+H_2$ for its total production. Its marginal costs are
--
--   $$MC_1=\alpha_1H_1,\qquad MC_2=\alpha_1H_1+\alpha_2(\mathcal H-H_1)$$
--
--   (Eqs. (1)–(2)), with slopes $\alpha_1$ for scheduled and $\alpha_2$ for adjusted production. This module defines:
--
--   1. **The HCG's overall cost** (Eq. (3), first expression), the area under the marginal-cost curves:
--   $$C(H_1,H_2)=\int_0^{H_1}\alpha_1h\,dh+\int_{H_1}^{\mathcal H}\big[\alpha_1H_1+\alpha_2(h-H_1)\big]\,dh.$$
--   2. **The deadweight loss** (Eq. (4), first expression), the extra cost of producing $\mathcal H$ partly as an adjustment rather than scheduling it all in Stage 1:
--   $$DWL=C(H_1,H_2)-C(\mathcal H,0).$$
--
--   The closed forms $C=\alpha_1\mathcal H^2/2+(\alpha_2-\alpha_1)H_2^2/2$ and $DWL=(\alpha_2-\alpha_1)H_2^2/2$ are theorems of the mission, not part of the definition.
--
--   **Formalization Note** Both integrals are oriented interval integrals, so for $H_2<0$ the second integral is negative, as in Figure 1 (right) of the paper. The marginal costs are linear as printed, with no floor at zero, and the cost is defined for all real $H_1,H_2$ (the paper has $H_1\in[0,1]$).
-- source:
--   Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, Optimal Electricity Imbalance Pricing for the Emerging Penetration of Renewable and Low-Cost Generators, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2021.0555, §3.1.2, Eqs. (1)–(3), p.6 (PDF p.8); §3.2, Eq. (4), p.7 (PDF p.9)

import Mathlib

namespace ImbalPricing

/-- **Overall production cost of the high-cost generator (HCG)**, Ghiassi-Farrokhfal, Belo,
Hesamzadeh, Bunn, *Optimal Electricity Imbalance Pricing …*, MSOM Articles in Advance (2023),
§3.1.2, Eq. (3) (first expression), p.6 (PDF p.8): the area under the marginal-cost curves
`MC₁ = α₁ H₁` (Eq. (1)) and `MC₂ = α₁ H₁ + α₂ (𝓗 − H₁)` (Eq. (2)),
`C(H₁, H₂) = ∫₀^{H₁} α₁ h dh + ∫_{H₁}^{𝓗} [α₁ H₁ + α₂ (h − H₁)] dh`, with `𝓗 = H₁ + H₂`.

Here `H₁` is the HCG's production scheduled in Stage 1 and `H₂` its adjustment in Stage 2.

**Formalization Note.** Both integrals are oriented interval integrals (`∫ h in a..b`), so for
`H₂ < 0` the second integral is negative, as in Figure 1 (right) of the paper. The marginal costs
are linear as printed in Eqs. (1)–(3), with no floor at zero. The cost is defined for all real
`H₁, H₂`; the paper has `H₁ ∈ [0, 1]`. -/
noncomputable def hcgCost (α₁ α₂ H₁ H₂ : ℝ) : ℝ :=
  (∫ h in (0 : ℝ)..H₁, α₁ * h) + ∫ h in H₁..(H₁ + H₂), (α₁ * H₁ + α₂ * (h - H₁))

/-- **Deadweight loss (DWL)**, MSOM Articles in Advance (2023), §3.2, Eq. (4) (first
expression), p.7 (PDF p.9): `DWL = C(H₁, H₂) − C(𝓗, 0)` with `𝓗 = H₁ + H₂`, the extra cost of
producing the total `𝓗` with an adjustment `H₂` instead of scheduling it all in Stage 1. -/
noncomputable def dwl (α₁ α₂ H₁ H₂ : ℝ) : ℝ :=
  hcgCost α₁ α₂ H₁ H₂ - hcgCost α₁ α₂ (H₁ + H₂) 0

end ImbalPricing


