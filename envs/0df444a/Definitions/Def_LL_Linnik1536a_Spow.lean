-- Prove2me | Definitions.Def_LL_Linnik1536a_Spow
-- name    : LL_Linnik1536a_Spow
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-27T21:42:25.388742+00:00
-- url     : https://prove2.me/theorems/96974e8a-2d5a-4d6a-8194-2794a57b15c0
-- title:
--   Its real part $S_L(x)$
-- statement:
--   $S_L(x)=\sum_{j=0}^{L-1}\cos(2\pi 2^j x)$, the real part of $G_L(x)$.

import Mathlib

namespace LL_Linnik1536a
open Real MeasureTheory Finset

noncomputable def Spow (L : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range L, Real.cos (2 * π * ((2 : ℝ) ^ j * x))

end LL_Linnik1536a


