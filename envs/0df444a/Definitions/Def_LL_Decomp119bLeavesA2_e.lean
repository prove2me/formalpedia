-- Prove2me | Definitions.Def_LL_Decomp119bLeavesA2_e
-- name    : LL_Decomp119bLeavesA2_e
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:06:30.345027+00:00
-- url     : https://prove2.me/theorems/67a49fe3-2bec-4620-b78c-b30bbeba9de0
-- title:
--   The additive character $e(t)=e^{2\pi i t}$
-- statement:
--   For real $t$, $e(t)=\exp(2\pi i t)$.

import Mathlib

namespace LL_Decomp119bLeavesA2

noncomputable section

open scoped ArithmeticFunction

noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

end

end LL_Decomp119bLeavesA2


