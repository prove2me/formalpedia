-- Prove2me | Definitions.Def_LL_Gauss_upper_window_low_e
-- name    : LL_Gauss_upper_window_low_e
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:51:34.682658+00:00
-- url     : https://prove2.me/theorems/06c14220-db29-4ff2-a52b-e20a0cad5800
-- title:
--   The additive character $e(t)=e^{2\pi i t}$
-- statement:
--   For real $t$, the complex number $e(t)=\exp(2\pi i t)$.

import Mathlib

namespace LL_Gauss_upper_window_low

noncomputable section

open scoped ArithmeticFunction

noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

end

end LL_Gauss_upper_window_low


