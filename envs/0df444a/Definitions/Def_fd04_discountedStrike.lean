-- Prove2me | Definitions.Def_fd04_discountedStrike
-- name    : fd04_discountedStrike
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T10:45:18.180088+00:00
-- url     : https://prove2.me/theorems/a19e2e1a-f27a-4c40-8adf-56344ca27377
-- title:
--   Choice-date discounted strike
-- statement:
--   The value at a decision date of a strike K paid a further n periods later at gross bank growth R is K/R^n.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_BinomialMarket

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

/-- Strike discounted over the remaining binomial steps. -/
noncomputable def discountedStrike (m : BinomialMarket) (K : ℝ) (n : ℕ) : ℝ :=
  K / m.growth ^ n

end FinancialDerivatives.FD04


