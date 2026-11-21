-- Prove2me | Definitions.Def_LL_Burst9MatrixR3_sigma0
-- name    : LL_Burst9MatrixR3_sigma0
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:45:35.247961+00:00
-- url     : https://prove2.me/theorems/1958f86e-a3c1-43ba-8086-56c70eabcef5
-- title:
--   Wu's normalized function $\sigma_0(t)$
-- statement:
--   $\sigma_0(t)=\sigma(3,t+2,t+1)/\bigl(1-\sigma(3,5,4)\bigr)$, the normalized integral appearing in both kernels; the denominator is a fixed real constant. Real division by 0 would give 0.

import Mathlib
import Definitions.Def_LL_Burst9MatrixR3_sigma

namespace LL_Burst9MatrixR3

noncomputable section

open Real Finset Set MeasureTheory intervalIntegral

def sigma0 (t : ℝ) : ℝ := sigma 3 (t + 2) (t + 1) / (1 - sigma 3 5 4)

end

end LL_Burst9MatrixR3


