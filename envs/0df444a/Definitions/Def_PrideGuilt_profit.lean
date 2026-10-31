-- Prove2me | Definitions.Def_PrideGuilt_profit
-- name    : PrideGuilt_profit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:56.180268+00:00
-- url     : https://prove2.me/theorems/b9b7d061-c673-4651-af01-2e2bb17844a5
-- title:
--   Manufacturer's profit $\Pi(p,f)$
-- statement:
--   The manufacturer's profit (4) is demand times unit profit:
--
--   $$
--   \Pi(p,f)=D(p,f)\cdot u(p,f).
--   $$
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), eq. (4), p.11

import Mathlib
import Definitions.Def_PrideGuilt_demand
import Definitions.Def_PrideGuilt_unitProfit

namespace PrideGuilt

/-- **The manufacturer's profit (4), `Π(p, f) = D(p, f) · u(p, f)`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, eq. (4), p.11 (PDF 12). -/
noncomputable def profit (P : Params) (γP γG p f : ℝ) : ℝ :=
  demand P γP γG p f * unitProfit P γP γG p f

end PrideGuilt


