-- Prove2me | Definitions.Def_LL_SquareWave1124_sqW
-- name    : LL_SquareWave1124_sqW
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-27T05:48:50.945205+00:00
-- url     : https://prove2.me/theorems/38c81c4c-9027-4d0a-ba97-1eec6840a097
-- title:
--   The coefficient weight $W_\Delta(h)$
-- statement:
--   sqW Δ h is $1$ when $h=0$ and $\min(1/|h|,\,1/(\Delta h^2))$ otherwise.

import Mathlib

namespace LL_SquareWave1124

noncomputable section

noncomputable def sqW (Δ : ℝ) (h : ℤ) : ℝ :=
  if h = 0 then 1 else min (1 / |(h : ℝ)|) (1 / (Δ * (h : ℝ) ^ 2))

end

end LL_SquareWave1124


