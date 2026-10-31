-- Prove2me | Definitions.Def_PrideGuilt_dc
-- name    : PrideGuilt_dc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:44.268885+00:00
-- url     : https://prove2.me/theorems/f553f25a-a54e-44ff-99c9-5d47cf4604f1
-- title:
--   Unit cost saving of remanufacturing $\Delta c=c_n-c_u$
-- statement:
--   The unit cost saving from remanufacturing is
--
--   $$
--   \Delta c \equiv c_n - c_u ,
--   $$
--
--   the difference between the unit cost of a new product and of a remanufactured one. The quantity $c_r-\Delta c$ is the difficulty of remanufacturing (DOR) that delimits the regions $\Omega_1$–$\Omega_4$.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), below eq. (5), p.12

import Mathlib
import Definitions.Def_PrideGuilt_Params

namespace PrideGuilt

/-- **The unit cost saving of remanufacturing, `Δc ≡ c_n − c_u`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, below (5), p.12 (PDF 13). -/
def dc (P : Params) : ℝ := P.cn - P.cu

end PrideGuilt


