-- Prove2me | Definitions.Def_ImbalPricing_ExpectedDWL
-- name    : ImbalPricing_ExpectedDWL
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:25.854875+00:00
-- url     : https://prove2.me/theorems/731c8f9a-b1f4-4101-90e1-7a879981afa2
-- title:
--   Deadweight loss $DWL$ and expected deadweight loss $\mathbb E[DWL]$ at an offer profile
-- statement:
--   In the market of §3.1, at the offer profile $d$, the HCG schedules $H_1=1-L_1$ in Stage 1 and adjusts by $H_2=\epsilon-L_2$ in Stage 2. The realized **deadweight loss** is the deadweight loss of Eq. (4) at these quantities,
--   $$DWL(d)=C(H_1,H_2)-C(H_1+H_2,0),$$
--   a random variable, and the **expected deadweight loss** is $\mathbb E[DWL(d)]$, the quantity of Lemma 1 and Theorem 5.
--
--   **Formalization Note** The expectation is the Bochner integral against $\mu$.
-- source:
--   Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn, Optimal Electricity Imbalance Pricing for the Emerging Penetration of Renewable and Low-Cost Generators, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2021.0555, §3.2, Eq. (4), p.7 (PDF p.9) and Lemma 1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_ImbalPricing_HCGCost
import Definitions.Def_ImbalPricing_Market

open MeasureTheory

namespace ImbalPricing

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

namespace Market

/-- **Deadweight loss at an offer profile**, Ghiassi-Farrokhfal, Belo, Hesamzadeh, Bunn,
*Optimal Electricity Imbalance Pricing …*, MSOM Articles in Advance (2023), §3.2, Eq. (4), p.7
(PDF p.9): the realized `DWL = C(H₁, H₂) − C(𝓗, 0)` at the HCG's Stage-1 schedule `H₁ = 1 − L₁`
and Stage-2 adjustment `H₂ = ε − L₂` of the offer profile `d`, in outcome `ω`. -/
noncomputable def DWL (M : Market Ω N) (d : Fin N → ℝ) (ω : Ω) : ℝ :=
  dwl M.α₁ M.α₂ (M.H1 d) (M.H2 d ω)

/-- **Expected deadweight loss** `E[DWL]` at the offer profile `d` (Lemma 1, p.8, PDF p.10),
the Bochner integral of `DWL` against `μ`. -/
noncomputable def expectedDWL (M : Market Ω N) (d : Fin N → ℝ) : ℝ :=
  ∫ ω, M.DWL d ω ∂M.μ

end Market

end ImbalPricing


