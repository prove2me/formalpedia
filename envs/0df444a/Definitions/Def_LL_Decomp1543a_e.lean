-- Prove2me | Definitions.Def_LL_Decomp1543a_e
-- name    : LL_Decomp1543a_e
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:30:40.509998+00:00
-- url     : https://prove2.me/theorems/ba8c993f-a379-4816-901f-98281904f685
-- title:
--   Additive exponential
-- statement:
--   For real $x$, define $e(x)=\exp(2\pi i x)$.

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)
end LL_Decomp1543a


