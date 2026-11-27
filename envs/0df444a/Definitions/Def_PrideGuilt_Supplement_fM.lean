-- Prove2me | Definitions.Def_PrideGuilt_Supplement_fM
-- name    : PrideGuilt_Supplement_fM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:22:23.304628+00:00
-- url     : https://prove2.me/theorems/d300691d-763c-4674-ab29-cb8680f902a7
-- title:
--   Reward $f_m$, the highest reward compatible with an interior recycling rate
-- statement:
--   With the demand coefficients $b_0,b_1$, the cost saving $\Delta c$ and the guilt parameter $\gamma_G$,
--
--   $$
--   f_m\;=\;\Delta c-\frac{\gamma_G b_1}{b_0}.
--   $$
--
--   The paper describes $f_m$ as the highest reward the manufacturer can afford while inducing an interior recycling rate.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), §4, p.13

import Mathlib
import Definitions.Def_PrideGuilt_dc

namespace PrideGuilt.Supplement

open PrideGuilt

/-- **The highest reward compatible with an interior recycling rate, `f_m ≡ Δc − γ_Gb₁/b₀`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, §4, p.13 (PDF 14). -/
noncomputable def fM (P : Params) (γG : ℝ) : ℝ := dc P - γG * P.b1 / P.b0

end PrideGuilt.Supplement


