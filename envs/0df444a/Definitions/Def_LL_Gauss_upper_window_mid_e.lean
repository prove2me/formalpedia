-- Prove2me | Definitions.Def_LL_Gauss_upper_window_mid_e
-- name    : LL_Gauss_upper_window_mid_e
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:55:01.173182+00:00
-- url     : https://prove2.me/theorems/ec86faca-5433-4eb8-9ce9-11668c8e43fd
-- title:
--   The additive character $e(t)=e^{2\pi i t}$
-- statement:
--   For real $t$, the complex number $e(t)=\exp(2\pi i t)$.

import Mathlib

namespace LL_Gauss_upper_window_mid

noncomputable section

open scoped ArithmeticFunction

noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

end

end LL_Gauss_upper_window_mid


