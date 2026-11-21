-- Prove2me | Definitions.Def_LL_Gauss_lower_window_high_e
-- name    : LL_Gauss_lower_window_high_e
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:58:44.143176+00:00
-- url     : https://prove2.me/theorems/5878d5c1-bf19-4ebb-be59-0859b35d908c
-- title:
--   The additive character $e(t)=e^{2\pi i t}$
-- statement:
--   For real $t$, the complex number $e(t)=\exp(2\pi i t)$.

import Mathlib

namespace LL_Gauss_lower_window_high

noncomputable section

open scoped ArithmeticFunction

noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

end

end LL_Gauss_lower_window_high


