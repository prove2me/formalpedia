-- Prove2me | Definitions.Def_fd04_chooserInitialValue
-- name    : fd04_chooserInitialValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:46:24.547856+00:00
-- url     : https://prove2.me/theorems/3a457981-67ba-4623-9ced-b2702e1721ab
-- title:
--   Time-zero price of a simple chooser
-- statement:
--   Backward-induction price at inception of the choice-date maximum, allowing an arbitrary finite choice horizon.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_terminalStockTree
import Definitions.Def_fd04_chooserAtChoice

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

/-- A chooser is the European claim paying the decision-time maximum. -/
noncomputable def chooserInitialValue (m : BinomialMarket) (K : ℝ)
    (choiceSteps postChoiceSteps : ℕ) : ℝ :=
  europeanValue m choiceSteps
    (payoffTreeMap (chooserAtChoice m K postChoiceSteps) choiceSteps
      (terminalStockTree m choiceSteps m.initialSpot))

end FinancialDerivatives.FD04


