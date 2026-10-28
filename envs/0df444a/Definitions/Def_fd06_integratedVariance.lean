-- Prove2me | Definitions.Def_fd06_integratedVariance
-- name    : fd06_integratedVariance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:16:49.706563+00:00
-- url     : https://prove2.me/theorems/615a3282-057b-4cc3-b2c1-5732f6dd74d9
-- title:
--   Integrated squared volatility
-- statement:
--   Integrated squared volatility
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib

open MeasureTheory intervalIntegral

namespace FinancialDerivatives.FD06

/-- Integrated squared volatility. -/
noncomputable def integratedVariance (σ : ℝ → ℝ) (t T : ℝ) : ℝ := ∫ u in t..T, (σ u) ^ 2

end FinancialDerivatives.FD06


