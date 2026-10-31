-- Prove2me | Definitions.Def_PrideGuilt_benchPrice
-- name    : PrideGuilt_benchPrice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:44.178968+00:00
-- url     : https://prove2.me/theorems/e8462831-bdc8-4bdb-be69-3a4f319c58db
-- title:
--   Benchmark price $p_0$
-- statement:
--   The benchmark price (6) is
--
--   $$
--   p_0=\frac{1-b_1I_G}{2b_0}+\frac{c_n}{2}.
--   $$
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), eq. (6), p.12

import Mathlib
import Definitions.Def_PrideGuilt_Params

namespace PrideGuilt

/-- **The benchmark price (6), `p₀ = (1 − b₁I_G)/(2b₀) + c_n/2`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, eq. (6), p.12 (PDF 13). -/
noncomputable def benchPrice (P : Params) : ℝ := (1 - P.b1 * P.IG) / (2 * P.b0) + P.cn / 2

end PrideGuilt


