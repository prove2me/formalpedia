-- Prove2me | Definitions.Def_fd04_putInitialValue
-- name    : fd04_putInitialValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:46:57.710866+00:00
-- url     : https://prove2.me/theorems/774bb255-ce67-4981-bd8a-9e650c2731c5
-- title:
--   Inception European put price
-- statement:
--   Value of a vanilla European put with n periods to maturity, struck at K and valued from the initial spot.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_putAtChoice

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

/-- Inception put premium. -/
noncomputable def putInitialValue (m : BinomialMarket) (K : ℝ)
    (n : ℕ) : ℝ := putAtChoice m K n m.initialSpot

end FinancialDerivatives.FD04


