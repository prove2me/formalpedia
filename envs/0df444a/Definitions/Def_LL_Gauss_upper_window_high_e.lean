-- Prove2me | Definitions.Def_LL_Gauss_upper_window_high_e
-- name    : LL_Gauss_upper_window_high_e
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:47:40.264416+00:00
-- url     : https://prove2.me/theorems/57e1e96a-5b11-432b-b320-4037c3e3fcaa
-- title:
--   The additive character $e(t)=e^{2\pi i t}$
-- statement:
--   For real $t$, the complex number $e(t)=\exp(2\pi i t)$.

import Mathlib

namespace LL_Gauss_upper_window_high

noncomputable section

open scoped ArithmeticFunction

noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

end

end LL_Gauss_upper_window_high


