-- Prove2me | Definitions.Def_fd02_riskNeutralUp
-- name    : fd02_riskNeutralUp
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:36:57.743967+00:00
-- url     : https://prove2.me/theorems/00abd2f6-642b-4ec6-8a81-3ab246ff93a0
-- title:
--   Risk-neutral up probability from stock and bank factors
-- statement:
--   The candidate up-state risk-neutral weight is (R-d)/(u-d), with positivity to be derived from no-arbitrage.
-- source:
--   Original derived definition based on Wilmott, Howison and Dewynne (1995), §10.2, equation (10.8), printed p. 184; https://doi.org/10.1017/CBO9780511812545. The same object is fixed for all FD-02 theorem statements.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket

namespace FinancialDerivatives.FD02

/-- Unique candidate up weight from the stock martingale equation. -/
noncomputable def riskNeutralUp (m : TwoStateMarket) : ℝ :=
  (m.growth - m.down) / (m.up - m.down)

end FinancialDerivatives.FD02


