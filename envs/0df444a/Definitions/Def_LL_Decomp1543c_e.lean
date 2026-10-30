-- Prove2me | Definitions.Def_LL_Decomp1543c_e
-- name    : LL_Decomp1543c_e
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T17:27:19.426771+00:00
-- url     : https://prove2.me/theorems/b0f29e5c-1279-4fc6-b93c-df22979401ad
-- title:
--   The additive character
-- statement:
--   For real $x$, $e(x)=\exp(2\pi i x)$.

import Mathlib

namespace LL_Decomp1543c

open Real Finset ArithmeticFunction

noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

end LL_Decomp1543c


