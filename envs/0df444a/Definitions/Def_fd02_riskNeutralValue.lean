-- Prove2me | Definitions.Def_fd02_riskNeutralValue
-- name    : fd02_riskNeutralValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:38:53.370287+00:00
-- url     : https://prove2.me/theorems/066d9eb6-9b10-4395-953f-e10674b91938
-- title:
--   Discounted one-period risk-neutral claim valuation
-- statement:
--   The one-period proposed price is the up/down payoff average weighted by risk-neutral probabilities and divided by the bank accumulation factor.
-- source:
--   Original derived definition based on Wilmott, Howison and Dewynne (1995), §10.1, equation (10.2), and §10.3, printed pp. 182 and 187; https://doi.org/10.1017/CBO9780511812545. The same object is fixed for all FD-02 theorem statements.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp

namespace FinancialDerivatives.FD02

/-- Discounted two-state expectation under the candidate martingale weights. -/
noncomputable def riskNeutralValue (m : TwoStateMarket) (H : Bool → ℝ) : ℝ :=
  (riskNeutralUp m * H true + (1 - riskNeutralUp m) * H false) / m.growth

end FinancialDerivatives.FD02


