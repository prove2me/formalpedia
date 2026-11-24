-- Prove2me | Definitions.Def_LL_Decomp269bLeavesVeryLow_e
-- name    : LL_Decomp269bLeavesVeryLow_e
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:06:39.251105+00:00
-- url     : https://prove2.me/theorems/f8084fde-465f-4505-b5ac-16bdae8b3f83
-- title:
--   The additive character $e(t)=e^{2\pi i t}$
-- statement:
--   For real $t$, $e(t)=\exp(2\pi i t)$, a complex number of modulus one.

import Mathlib

namespace LL_Decomp269bLeavesVeryLow

noncomputable section

open scoped ArithmeticFunction

noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

end

end LL_Decomp269bLeavesVeryLow


