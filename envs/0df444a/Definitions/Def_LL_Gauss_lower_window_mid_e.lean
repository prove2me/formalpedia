-- Prove2me | Definitions.Def_LL_Gauss_lower_window_mid_e
-- name    : LL_Gauss_lower_window_mid_e
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T08:01:54.013524+00:00
-- url     : https://prove2.me/theorems/17895e2d-c63e-4a16-b281-1fe51d80a6c3
-- title:
--   The additive character $e(t)=e^{2\pi i t}$
-- statement:
--   For real $t$, the complex number $e(t)=\exp(2\pi i t)$.

import Mathlib

namespace LL_Gauss_lower_window_mid

noncomputable section

open scoped ArithmeticFunction

noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

end

end LL_Gauss_lower_window_mid


