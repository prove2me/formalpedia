-- Prove2me | Definitions.Def_fd03_hedgeShiftBank
-- name    : fd03_hedgeShiftBank
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:04:47.315073+00:00
-- url     : https://prove2.me/theorems/9744196b-fc46-46c7-841e-505e7577630f
-- title:
--   Shift a self-financing hedge by an additional bank deposit
-- statement:
--   Adding current cash c to the bank account of a hedge adds c to its node wealth. At every subsequent node, the additional bank deposit has grown by the factor R for each elapsed period. The stock holdings remain unchanged, preserving a self-financing hedge while carrying additional bank wealth.
-- source:
--   Original finite-riskless-account transformation supporting discrete writer superhedges; market conventions as in Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.5, printed pp. 182–191.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd03_HedgeTree

namespace FinancialDerivatives.FD03

/-- Add an initial bank deposit, grown consistently along both descendants. -/
noncomputable def hedgeShiftBank (m : BinomialMarket) :
    (n : ℕ) → ℝ → HedgeTree n → HedgeTree n
  | 0, extra, .terminal cash => .terminal (cash + extra)
  | n + 1, extra, .node shares bank up down =>
      .node shares (bank + extra)
        (hedgeShiftBank m n (extra * m.growth) up)
        (hedgeShiftBank m n (extra * m.growth) down)

end FinancialDerivatives.FD03


