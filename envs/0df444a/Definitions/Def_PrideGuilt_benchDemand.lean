-- Prove2me | Definitions.Def_PrideGuilt_benchDemand
-- name    : PrideGuilt_benchDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:45.959072+00:00
-- url     : https://prove2.me/theorems/f3dd73ed-0c1c-418c-9084-90dabbae0485
-- title:
--   Benchmark demand $\tilde D(p)$
-- statement:
--   Without remanufacturing the manufacturer offers no reward, and every consumer bears the intrinsic guilt of not recycling. The demand is then
--
--   $$
--   \tilde D(p)=1-b_0p-b_1I_G .
--   $$
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), §4, p.12

import Mathlib
import Definitions.Def_PrideGuilt_Params

namespace PrideGuilt

/-- **The benchmark demand without remanufacturing, `D̃(p) = 1 − b₀p − b₁I_G`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, §4, p.12 (PDF 13). -/
def benchDemand (P : Params) (p : ℝ) : ℝ := 1 - P.b0 * p - P.b1 * P.IG

end PrideGuilt


