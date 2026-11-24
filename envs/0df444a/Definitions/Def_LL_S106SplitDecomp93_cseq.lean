-- Prove2me | Definitions.Def_LL_S106SplitDecomp93_cseq
-- name    : LL_S106SplitDecomp93_cseq
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:19:40.563179+00:00
-- url     : https://prove2.me/theorems/74b9ffe4-454a-45a8-aa14-dcfc02de2bed
-- title:
--   The Stieltjes approximants $c_n$
-- statement:
--   For a natural number $n$, $c_n=\sum_{m\le n}\log m/m-\tfrac12\log^2 n-\log n/(2n)$; these converge to the first Stieltjes constant.

import Mathlib
import Definitions.Def_LL_S106SplitDecomp93_Lsum

namespace LL_S106SplitDecomp93

noncomputable section

open Real Finset Filter Topology

noncomputable def cseq (n : ℕ) : ℝ := Lsum n - Real.log n ^ 2 / 2 - Real.log n / (2 * n)

end

end LL_S106SplitDecomp93


