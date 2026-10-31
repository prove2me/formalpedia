-- Prove2me | Definitions.Def_PrideGuilt_UN
-- name    : PrideGuilt_UN
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:52.878293+00:00
-- url     : https://prove2.me/theorems/fe42ab21-010e-44b5-afdc-8909b61e13a0
-- title:
--   Expected utility of a non-recycler $U_N$
-- statement:
--   A non-recycler feels the intrinsic guilt $I_G$ and the social guilt $\gamma_G$ when meeting a recycler, which happens with probability $\tau$. Its expected utility (2) is
--
--   $$
--   U_N(\tau) = -\tau\gamma_G - I_G .
--   $$
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), eq. (2), p.7

import Mathlib
import Definitions.Def_PrideGuilt_Params

namespace PrideGuilt

/-- **A non-recycler's expected utility (2), `U_N = −τγ_G − I_G`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, eq. (2), p.7 (PDF 8).
`τ` is the recycling rate and `γG` the socially influenced guilt. -/
def UN (P : Params) (γG τ : ℝ) : ℝ := -τ * γG - P.IG

end PrideGuilt


