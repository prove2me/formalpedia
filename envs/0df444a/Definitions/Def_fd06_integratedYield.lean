-- Prove2me | Definitions.Def_fd06_integratedYield
-- name    : fd06_integratedYield
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:16:32.831519+00:00
-- url     : https://prove2.me/theorems/d264fb62-163f-4200-ade6-b5d6b961ae25
-- title:
--   Deterministic continuous dividend yield integrated over time
-- statement:
--   Deterministic continuous dividend yield integrated over time
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib

open MeasureTheory intervalIntegral

namespace FinancialDerivatives.FD06

/-- Deterministic continuous dividend yield integrated over time. -/
noncomputable def integratedYield (q : ℝ → ℝ) (t T : ℝ) : ℝ := ∫ u in t..T, q u

end FinancialDerivatives.FD06


