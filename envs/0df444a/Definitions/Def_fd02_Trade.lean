-- Prove2me | Definitions.Def_fd02_Trade
-- name    : fd02_Trade
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:35:57.355986+00:00
-- url     : https://prove2.me/theorems/5d1d2e00-46cd-47e1-85c4-d6fa1514eb46
-- title:
--   Signed stock and bank holdings
-- statement:
--   A buy-and-hold strategy consists of unrestricted real stock holdings and real units of the bank account. Negative values represent short-selling or borrowing.
-- source:
--   Original derived definition based on Wilmott, Howison and Dewynne (1995), §§2.4,3.2, printed pp. 30–34; https://doi.org/10.1017/CBO9780511812545. The same object is fixed for all FD-02 theorem statements.

import Mathlib.Data.Real.Basic

namespace FinancialDerivatives.FD02

/-- Signed holdings in the stock and the unit-price bank account. -/
structure Trade where
  shares : ℝ
  cash : ℝ

end FinancialDerivatives.FD02


