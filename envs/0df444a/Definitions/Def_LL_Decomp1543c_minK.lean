-- Prove2me | Definitions.Def_LL_Decomp1543c_minK
-- name    : LL_Decomp1543c_minK
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T17:27:59.354199+00:00
-- url     : https://prove2.me/theorems/a6b3f0af-3ae1-488a-ae24-59add6841108
-- title:
--   The truncated reciprocal distance kernel
-- statement:
--   For real $X,\theta$, $K(X,\theta)=X$ if $\|\theta\|=0$, and $K(X,\theta)=\min(X,1/(2\|\theta\|))$ otherwise.

import Mathlib
import Definitions.Def_LL_Decomp1543c_nint

namespace LL_Decomp1543c

open Real Finset ArithmeticFunction

noncomputable def minK (X θ : ℝ) : ℝ := if nint θ = 0 then X else min X (1 / (2 * nint θ))

end LL_Decomp1543c


