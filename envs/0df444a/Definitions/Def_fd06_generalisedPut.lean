-- Prove2me | Definitions.Def_fd06_generalisedPut
-- name    : fd06_generalisedPut
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:18:54.5826+00:00
-- url     : https://prove2.me/theorems/5796f826-7e27-4767-8875-d9a615ea85b3
-- title:
--   Closed-form put under integrated carry and variance
-- statement:
--   Closed-form put under integrated carry and variance
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib
import Definitions.Def_fd06_standardNormalCDF
import Definitions.Def_fd06_generalisedD1
import Definitions.Def_fd06_generalisedD2

namespace FinancialDerivatives.FD06

/-- Closed-form put under integrated carry and variance. -/
noncomputable def generalisedPut (S K R Q V : ℝ) : ℝ := K * Real.exp (-R) * standardNormalCDF (-generalisedD2 S K R Q V) - S * Real.exp (-Q) * standardNormalCDF (-generalisedD1 S K R Q V)

end FinancialDerivatives.FD06


