-- Prove2me | Definitions.Def_PrideGuilt_demand
-- name    : PrideGuilt_demand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:02.733532+00:00
-- url     : https://prove2.me/theorems/e8bdaef6-3f2c-4bae-9c6a-b2647d912f9c
-- title:
--   Demand $D(p,f)$
-- statement:
--   For a selling price $p$ and a recycling reward $f$ the manufacturer's demand (3) is
--
--   $$
--   D(p,f)=1-b_0p+b_1\bar U(f).
--   $$
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), eq. (3), p.11

import Mathlib
import Definitions.Def_PrideGuilt_Ubar

namespace PrideGuilt

/-- **The demand (3), `D(p, f) = 1 − b₀p + b₁Ū(f)`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, eq. (3), p.11 (PDF 12). -/
noncomputable def demand (P : Params) (γP γG p f : ℝ) : ℝ := 1 - P.b0 * p + P.b1 * Ubar P γP γG f

end PrideGuilt


