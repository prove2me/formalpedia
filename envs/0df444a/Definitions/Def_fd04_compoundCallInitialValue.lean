-- Prove2me | Definitions.Def_fd04_compoundCallInitialValue
-- name    : fd04_compoundCallInitialValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:47:26.875379+00:00
-- url     : https://prove2.me/theorems/a8c37a48-ae34-4831-8061-c8cb87a82cef
-- title:
--   Inception price of a compound call-on-call
-- statement:
--   FD-03 European valuation of the call-on-call exercise payment at the earlier compound expiry.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_terminalStockTree
import Definitions.Def_fd04_compoundCallOnCallAtChoice

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

/-- Inception premium of a call on a later European call. -/
noncomputable def compoundCallInitialValue (m : BinomialMarket)
    (K L : ℝ) (exerciseSteps postExerciseSteps : ℕ) : ℝ :=
  europeanValue m exerciseSteps
    (payoffTreeMap (compoundCallOnCallAtChoice m K L postExerciseSteps)
      exerciseSteps (terminalStockTree m exerciseSteps m.initialSpot))

end FinancialDerivatives.FD04


