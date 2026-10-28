-- Prove2me | Definitions.Def_fd06_generalisedD1
-- name    : fd06_generalisedD1
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:17:14.13273+00:00
-- url     : https://prove2.me/theorems/a1ff21b7-4d2e-4cd6-b798-aef5583220dd
-- title:
--   Generalised Black-Scholes d1
-- statement:
--   Generalised Black-Scholes d1
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib

namespace FinancialDerivatives.FD06

/-- Generalised Black-Scholes d1. -/
noncomputable def generalisedD1 (S K R Q V : ℝ) : ℝ := (Real.log (S / K) + R - Q + V / 2) / Real.sqrt V

end FinancialDerivatives.FD06


