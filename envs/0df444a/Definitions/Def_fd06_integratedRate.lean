-- Prove2me | Definitions.Def_fd06_integratedRate
-- name    : fd06_integratedRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:16:18.398559+00:00
-- url     : https://prove2.me/theorems/ec8a8765-b0c3-4533-bff2-844f1862d075
-- title:
--   Deterministic short rate integrated over time
-- statement:
--   Deterministic short rate integrated over time
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib

open MeasureTheory intervalIntegral

namespace FinancialDerivatives.FD06

/-- Deterministic short rate integrated over time. -/
noncomputable def integratedRate (r : ℝ → ℝ) (t T : ℝ) : ℝ := ∫ u in t..T, r u

end FinancialDerivatives.FD06


