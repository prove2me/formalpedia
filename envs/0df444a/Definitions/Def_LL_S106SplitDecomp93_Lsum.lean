-- Prove2me | Definitions.Def_LL_S106SplitDecomp93_Lsum
-- name    : LL_S106SplitDecomp93_Lsum
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:04:06.123+00:00
-- url     : https://prove2.me/theorems/c5b696b3-f3d1-4750-8224-b8c8a2f2efad
-- title:
--   The partial sums $\sum_{m\le n}\log m/m$
-- statement:
--   For a natural number $n$, the sum of $\log m/m$ over $1\le m\le n$.

import Mathlib

namespace LL_S106SplitDecomp93

noncomputable section

open Real Finset Filter Topology

noncomputable def Lsum (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, Real.log m / m

end

end LL_S106SplitDecomp93


