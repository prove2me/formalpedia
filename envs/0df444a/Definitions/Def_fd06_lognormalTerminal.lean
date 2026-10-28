-- Prove2me | Definitions.Def_fd06_lognormalTerminal
-- name    : fd06_lognormalTerminal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:17:01.63632+00:00
-- url     : https://prove2.me/theorems/61b3f4b1-4e00-4aa1-91ac-ede9e3ba1ebe
-- title:
--   Lognormal terminal spot with dividend carry
-- statement:
--   Lognormal terminal spot with dividend carry
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib

namespace FinancialDerivatives.FD06

/-- Lognormal terminal spot with dividend carry. -/
noncomputable def lognormalTerminal (S R Q V z : ℝ) : ℝ := S * Real.exp (R - Q - V / 2 + Real.sqrt V * z)

end FinancialDerivatives.FD06


