-- Prove2me | Definitions.Def_PrideGuilt_benchProfit
-- name    : PrideGuilt_benchProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:52.509118+00:00
-- url     : https://prove2.me/theorems/732e785b-1745-4dfd-a97b-4d5b63f54bab
-- title:
--   Benchmark profit $\tilde\Pi(p)$
-- statement:
--   Without remanufacturing every unit is new, and the profit at price $p$ is
--
--   $$
--   \tilde\Pi(p)=\tilde D(p)\,(p-c_n).
--   $$
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), §4, p.12

import Mathlib
import Definitions.Def_PrideGuilt_benchDemand

namespace PrideGuilt

/-- **The benchmark profit without remanufacturing, `Π̃(p) = D̃(p)(p − c_n)`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, §4, p.12 (PDF 13). -/
def benchProfit (P : Params) (p : ℝ) : ℝ := benchDemand P p * (p - P.cn)

end PrideGuilt


