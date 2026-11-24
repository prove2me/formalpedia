-- Prove2me | Definitions.Def_LL_S106SplitDecomp93_gamma1Seq
-- name    : LL_S106SplitDecomp93_gamma1Seq
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:32:30.698704+00:00
-- url     : https://prove2.me/theorems/ef552aad-6699-4cdf-a269-08bb747c8f02
-- title:
--   The lower approximants $u_j=c_{j+2}-1/(10\,(j+2))$
-- statement:
--   For a natural number $j$, $u_j=c_{j+2}-1/(10\,(j+2))$, an increasing sequence of lower approximations to the first Stieltjes constant.

import Mathlib
import Definitions.Def_LL_S106SplitDecomp93_cseq

namespace LL_S106SplitDecomp93

noncomputable section

open Real Finset Filter Topology

noncomputable def gamma1Seq (j : ℕ) : ℝ := cseq (j + 2) - 1 / (10 * ((j : ℝ) + 2))

end

end LL_S106SplitDecomp93


