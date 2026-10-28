-- Prove2me | Definitions.Def_fd04_chooserAtChoice
-- name    : fd04_chooserAtChoice
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:46:09.43202+00:00
-- url     : https://prove2.me/theorems/adc69754-bc9e-473d-85fc-416cc5ce4cc4
-- title:
--   Simple chooser value at the decision date
-- statement:
--   The holder chooses the more valuable of a same-strike European call and put with a common expiry.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_callAtChoice
import Definitions.Def_fd04_putAtChoice

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

/-- The holder receives the more valuable same-maturity option. -/
noncomputable def chooserAtChoice (m : BinomialMarket) (K : ℝ)
    (postChoiceSteps : ℕ) (spot : ℝ) : ℝ :=
  max (callAtChoice m K postChoiceSteps spot)
      (putAtChoice m K postChoiceSteps spot)

end FinancialDerivatives.FD04


