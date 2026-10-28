-- Prove2me | Definitions.Def_fd06_bsSpatialOperator
-- name    : fd06_bsSpatialOperator
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:20:18.198739+00:00
-- url     : https://prove2.me/theorems/b3b76f8e-e8f1-4f22-8e1f-e7892d1ac35d
-- title:
--   Spatial component of the Black-Scholes differential operator
-- statement:
--   Spatial component of the Black-Scholes differential operator
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib

namespace FinancialDerivatives.FD06

/-- Spatial component of the Black-Scholes differential operator. -/
noncomputable def bsSpatialOperator (S r q σ v vS vSS : ℝ) : ℝ := σ ^ 2 * S ^ 2 / 2 * vSS + (r - q) * S * vS - r * v

end FinancialDerivatives.FD06


