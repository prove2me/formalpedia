-- Prove2me | Definitions.Def_LL_Burst9MatrixR2_sigma0
-- name    : LL_Burst9MatrixR2_sigma0
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:34:33.499492+00:00
-- url     : https://prove2.me/theorems/e75f83f2-16f1-465a-927c-895e24d93dc1
-- title:
--   Wu's normalized function $\sigma_0(t)$
-- statement:
--   $\sigma_0(t)=\sigma(3,t+2,t+1)/\bigl(1-\sigma(3,5,4)\bigr)$, the normalized integral appearing in both kernels; the denominator is a fixed real constant. Real division by 0 would give 0.

import Mathlib
import Definitions.Def_LL_Burst9MatrixR2_sigma

namespace LL_Burst9MatrixR2

noncomputable section

open Real Finset Set MeasureTheory intervalIntegral

def sigma0 (t : ℝ) : ℝ := sigma 3 (t + 2) (t + 1) / (1 - sigma 3 5 4)

end

end LL_Burst9MatrixR2


