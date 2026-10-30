-- Prove2me | Definitions.Def_LL_Decomp1543a_minK
-- name    : LL_Decomp1543a_minK
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:31:31.024567+00:00
-- url     : https://prove2.me/theorems/8ec1d8f2-03da-40af-b8d2-1a3fe9c5e2b5
-- title:
--   Truncated reciprocal distance kernel
-- statement:
--   For real $X,\theta$, define $K(X,\theta)=X$ when $\operatorname{nint}(\theta)=0$, and otherwise $K(X,\theta)=\min\{X,1/(2\operatorname{nint}(\theta))\}$.

import Mathlib
import Definitions.Def_LL_Decomp1543a_nint

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
noncomputable def minK (X θ : ℝ) : ℝ := if nint θ = 0 then X else min X (1 / (2 * nint θ))
end LL_Decomp1543a


