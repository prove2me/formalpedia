-- Prove2me | Definitions.Def_fd04_callInitialValue
-- name    : fd04_callInitialValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:46:41.033081+00:00
-- url     : https://prove2.me/theorems/8ce20763-7245-457f-98b3-082c6db64634
-- title:
--   Inception European call price
-- statement:
--   Value of a vanilla European call with n periods to maturity, struck at K and valued from the initial spot.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_callAtChoice

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

/-- Inception call premium. -/
noncomputable def callInitialValue (m : BinomialMarket) (K : ℝ)
    (n : ℕ) : ℝ := callAtChoice m K n m.initialSpot

end FinancialDerivatives.FD04


