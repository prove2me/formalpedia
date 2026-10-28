-- Prove2me | Definitions.Def_fd04_putAtChoice
-- name    : fd04_putAtChoice
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:45:55.316685+00:00
-- url     : https://prove2.me/theorems/16787eac-d43e-44ad-85eb-8488bbd03965
-- title:
--   Remaining-maturity put value at decision time
-- statement:
--   A put's value conditional on current spot and a remaining n-step binomial horizon.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_terminalStockTree
import Definitions.Def_fd04_putPayoff

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

/-- The FD-03 European value of a later-expiring put. -/
noncomputable def putAtChoice (m : BinomialMarket) (K : ℝ)
    (n : ℕ) (spot : ℝ) : ℝ :=
  europeanValue m n
    (payoffTreeMap (putPayoff K) n (terminalStockTree m n spot))

end FinancialDerivatives.FD04


