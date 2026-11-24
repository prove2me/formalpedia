-- Prove2me | Definitions.Def_LL_S106SplitDecomp93_stieltjes1
-- name    : LL_S106SplitDecomp93_stieltjes1
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T15:45:42.674578+00:00
-- url     : https://prove2.me/theorems/7a788a06-975d-41e7-a73a-189aacd0fb77
-- title:
--   The first Stieltjes constant $\gamma_1$ as a supremum
-- statement:
--   $\gamma_1$ is defined as the supremum over natural numbers $j$ of $u_j=c_{j+2}-1/(10\,(j+2))$; this equals the first Stieltjes constant $\gamma_1=-0.0728158454\ldots$.

import Mathlib
import Definitions.Def_LL_S106SplitDecomp93_gamma1Seq

namespace LL_S106SplitDecomp93

noncomputable section

open Real Finset Filter Topology

noncomputable def stieltjes1 : ℝ := ⨆ j : ℕ, gamma1Seq j

end

end LL_S106SplitDecomp93


