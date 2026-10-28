-- Prove2me | Definitions.Def_fd05_vanillaTerminalTree
-- name    : fd05_vanillaTerminalTree
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:37:41.859979+00:00
-- url     : https://prove2.me/theorems/124086ca-e65d-4ed5-ba72-be1866f53934
-- title:
--   Vanilla terminal payoff tree derived from FD-03 stock tree
-- statement:
--   The vanilla tree applies the terminal reward to the FD-03 stock-price tree, preserving each full history.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket
import Definitions.Def_fd03_PayoffTree
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_terminalStockTree

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

/-- Vanilla reward on the actual full terminal stock tree. -/
noncomputable def vanillaTerminalTree (m : BinomialMarket) (N : ℕ)
    (g : ℝ → ℝ) : PayoffTree N :=
  payoffTreeMap g N (terminalStockTree m N m.initialSpot)

end FinancialDerivatives.FD05


