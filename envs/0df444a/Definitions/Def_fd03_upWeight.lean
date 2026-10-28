-- Prove2me | Definitions.Def_fd03_upWeight
-- name    : fd03_upWeight
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:54:30.190848+00:00
-- url     : https://prove2.me/theorems/cd98d8a0-7b9d-49d0-9cbe-d1506c5e3ce2
-- title:
--   Risk-neutral up-state weight in the repeated binomial market
-- statement:
--   The up-state pricing weight is q=(R-d)/(u-d), determined uniquely by no-arbitrage stock and bank growth. The strict market inequalities imply 0<q<1, which is proved separately rather than assumed in this definition.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.2, printed pp. 182–186. Risk-neutral probability in the single-step node-pricing calculation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket

namespace FinancialDerivatives.FD03

/-- The market-implied up-state risk-neutral weight. -/
noncomputable def upWeight (m : BinomialMarket) : ℝ :=
  (m.growth - m.down) / (m.up - m.down)

end FinancialDerivatives.FD03


