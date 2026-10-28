-- Prove2me | Definitions.Def_fd02_replicatingTrade
-- name    : fd02_replicatingTrade
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:39:11.051998+00:00
-- url     : https://prove2.me/theorems/a0805236-9326-450b-9461-b2f06d347a63
-- title:
--   Explicit delta-and-cash hedge for an arbitrary claim
-- statement:
--   The replicating stock and cash holdings are the unique solution to the two linear terminal payoff equations when the market is nondegenerate.
-- source:
--   Original derived definition based on Wilmott, Howison and Dewynne (1995), §2.4 and §10.3, printed pp. 30–31 and 187; https://doi.org/10.1017/CBO9780511812545. The same object is fixed for all FD-02 theorem statements.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade

namespace FinancialDerivatives.FD02

/-- Unique candidate hedge from solving the two terminal payoff equations. -/
noncomputable def replicatingTrade (m : TwoStateMarket) (H : Bool → ℝ) : Trade where
  shares := (H true - H false) / (m.spot * (m.up - m.down))
  cash := (m.up * H false - m.down * H true) / (m.growth * (m.up - m.down))

end FinancialDerivatives.FD02


