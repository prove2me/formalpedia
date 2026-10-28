-- Prove2me | Definitions.Def_fd04_callAtChoice
-- name    : fd04_callAtChoice
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:45:41.723366+00:00
-- url     : https://prove2.me/theorems/baa9135e-7c8f-4fbd-b645-43880891d377
-- title:
--   Remaining-maturity call value at decision time
-- statement:
--   A call's value conditional on current spot and a remaining n-step binomial horizon.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_terminalStockTree
import Definitions.Def_fd04_callPayoff

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

/-- The FD-03 European value of a later-expiring call. -/
noncomputable def callAtChoice (m : BinomialMarket) (K : ℝ)
    (n : ℕ) (spot : ℝ) : ℝ :=
  europeanValue m n
    (payoffTreeMap (callPayoff K) n (terminalStockTree m n spot))

end FinancialDerivatives.FD04


