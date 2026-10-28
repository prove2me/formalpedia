-- Prove2me | Definitions.Def_fd05_historyWeight
-- name    : fd05_historyWeight
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T17:14:03.482202+00:00
-- url     : https://prove2.me/theorems/a87c8b50-1c29-452b-954d-f94e365b0d6e
-- title:
--   Risk-neutral probability weight of a full history
-- statement:
--   A complete binomial history carries the product risk-neutral probability from the unique positive up and down weights.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd03_upWeight

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

/-- Product of q for upward moves and 1-q for downward moves. -/
noncomputable def historyWeight (m : BinomialMarket) (steps : List Bool) : ℝ :=
  (steps.map (fun b => if b then upWeight m else 1 - upWeight m)).prod

end FinancialDerivatives.FD05


