-- Prove2me | Definitions.Def_fd06_generalisedCall
-- name    : fd06_generalisedCall
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:18:24.036672+00:00
-- url     : https://prove2.me/theorems/67fdc31a-4361-475d-9ac3-4b57d5955348
-- title:
--   Closed-form call under integrated carry and variance
-- statement:
--   Closed-form call under integrated carry and variance
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib
import Definitions.Def_fd06_standardNormalCDF
import Definitions.Def_fd06_generalisedD1
import Definitions.Def_fd06_generalisedD2

namespace FinancialDerivatives.FD06

/-- Closed-form call under integrated carry and variance. -/
noncomputable def generalisedCall (S K R Q V : ℝ) : ℝ := S * Real.exp (-Q) * standardNormalCDF (generalisedD1 S K R Q V) - K * Real.exp (-R) * standardNormalCDF (generalisedD2 S K R Q V)

end FinancialDerivatives.FD06


