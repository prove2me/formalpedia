-- Prove2me | Definitions.Def_PrideGuilt_Supplement_InOmega1
-- name    : PrideGuilt_Supplement_InOmega1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:19:28.269092+00:00
-- url     : https://prove2.me/theorems/96927fff-d067-5c6e-b00c-fc3d9e0bc2ef
-- title:
--   Region $\Omega_1$ (very high degree of reluctance)
-- statement:
--   Fix the model parameters other than the socially influenced pride $\gamma_P$ and guilt $\gamma_G$, and write $c_r=c_e-I_P-I_G$ for the consumer's net cost of recycling and $\Delta c=c_n-c_u$ for the unit cost saving of remanufacturing; $c_r-\Delta c$ is the degree of reluctance (DOR). The region $\Omega_1$ is the set of pairs $(\gamma_P,\gamma_G)$ with
--
--   $$
--   c_r-\Delta c\ \ge\ \max(\gamma_P,\gamma_G)-\frac{b_1\gamma_G}{b_0}.
--   $$
--
--   In $\Omega_1$ the DOR dominates both socially influenced emotions, and Proposition 2 shows that the manufacturer does not remanufacture.
--
--   **Formalization Note** The set is stated exactly as printed. The paper omits the diagonal $\gamma_P=\gamma_G$ from every region (footnote 5); that exclusion is a hypothesis of the theorems that use $\Omega_1$, not part of this definition.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 2, p.13

import Mathlib
import Definitions.Def_PrideGuilt_cr
import Definitions.Def_PrideGuilt_dc

namespace PrideGuilt.Supplement

open PrideGuilt

/-- **The region `Ω₁` (very high degree of reluctance).**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 2, p.13 (PDF 14):
`Ω₁ ≡ {(γ_P, γ_G) | c_r − Δc ≥ max(γ_P, γ_G) − b₁γ_G/b₀}`.

**Formalization Note.** The set is stated exactly as printed. The paper's regions omit the
diagonal `γ_P = γ_G` (footnote 5, p.15); that exclusion is a hypothesis of the theorems that use
`Ω₁`, not part of this definition. -/
def InOmega1 (P : Params) (γP γG : ℝ) : Prop :=
  max γP γG - P.b1 * γG / P.b0 ≤ cr P - dc P

end PrideGuilt.Supplement


