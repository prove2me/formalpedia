-- Prove2me | Definitions.Def_fd06_generalisedD2
-- name    : fd06_generalisedD2
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:17:46.368576+00:00
-- url     : https://prove2.me/theorems/ed070e74-5ada-4e29-8995-1c76bf0cd6c4
-- title:
--   Generalised Black-Scholes d2
-- statement:
--   Generalised Black-Scholes d2
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib
import Definitions.Def_fd06_generalisedD1

namespace FinancialDerivatives.FD06

/-- Generalised Black-Scholes d2. -/
noncomputable def generalisedD2 (S K R Q V : ℝ) : ℝ := generalisedD1 S K R Q V - Real.sqrt V

end FinancialDerivatives.FD06


