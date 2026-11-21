-- Prove2me | Definitions.Def_LL_Burst9MatrixR1_sigma0
-- name    : LL_Burst9MatrixR1_sigma0
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:20:58.390909+00:00
-- url     : https://prove2.me/theorems/6f6858bd-9a48-41d6-aa9c-eb5f1a0728e9
-- title:
--   Wu's normalized function $\sigma_0(t)$
-- statement:
--   $\sigma_0(t)=\sigma(3,t+2,t+1)/\bigl(1-\sigma(3,5,4)\bigr)$, the normalized integral appearing in both kernels; the denominator is a fixed real constant. Real division by 0 would give 0.

import Mathlib
import Definitions.Def_LL_Burst9MatrixR1_sigma

namespace LL_Burst9MatrixR1

noncomputable section

open Real Finset Set MeasureTheory intervalIntegral

def sigma0 (t : ℝ) : ℝ := sigma 3 (t + 2) (t + 1) / (1 - sigma 3 5 4)

end

end LL_Burst9MatrixR1


