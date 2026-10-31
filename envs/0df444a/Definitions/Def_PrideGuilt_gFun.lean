-- Prove2me | Definitions.Def_PrideGuilt_gFun
-- name    : PrideGuilt_gFun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:47.578988+00:00
-- url     : https://prove2.me/theorems/220385ea-f715-40fe-93ae-f3b1d006ac57
-- title:
--   Remanufacturing benefit $g(f)$
-- statement:
--   For a reward $f$, the paper's remanufacturing benefit (8) is
--
--   $$
--   g(f)\equiv\frac{b_1}{b_0}\big(\bar U(f)+I_G\big)+\tau^*(f)(\Delta c-f).
--   $$
--
--   The first term is the demand gain from the consumers' utility relative to the benchmark, the second the expected cost saving per unit. Proposition 1 shows remanufacturing at reward $f$ beats the benchmark exactly when $g(f)>0$.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), eq. (8), p.12

import Mathlib
import Definitions.Def_PrideGuilt_Ubar
import Definitions.Def_PrideGuilt_tauStar
import Definitions.Def_PrideGuilt_dc

namespace PrideGuilt

/-- **The remanufacturing benefit (8), `g(f) ≡ (b₁/b₀)(Ū(f) + I_G) + τ*(f)(Δc − f)`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, eq. (8), p.12 (PDF 13). -/
noncomputable def gFun (P : Params) (γP γG f : ℝ) : ℝ :=
  P.b1 / P.b0 * (Ubar P γP γG f + P.IG) + tauStar P γP γG f * (dc P - f)

end PrideGuilt


