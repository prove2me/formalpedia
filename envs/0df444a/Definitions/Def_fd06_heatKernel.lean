-- Prove2me | Definitions.Def_fd06_heatKernel
-- name    : fd06_heatKernel
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T23:15:47.810569+00:00
-- url     : https://prove2.me/theorems/effda4f0-22a2-4c14-a4b1-d11af94ae056
-- title:
--   One-dimensional diffusivity-one heat kernel
-- statement:
--   One-dimensional diffusivity-one heat kernel
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic interpretation and rigorous extension.

import Mathlib

namespace FinancialDerivatives.FD06

/-- One-dimensional diffusivity-one heat kernel. -/
noncomputable def heatKernel (τ x : ℝ) : ℝ := Real.exp (-(x ^ 2) / (4 * τ)) / Real.sqrt (4 * Real.pi * τ)

end FinancialDerivatives.FD06


