-- Prove2me | Definitions.Def_LL_SchoenfeldLiS76_liPV
-- name    : LL_SchoenfeldLiS76_liPV
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-23T17:35:55.474711+00:00
-- url     : https://prove2.me/theorems/662efc7a-7ad2-4bc8-99b1-be677d77afa4
-- title:
--   Principal value logarithmic integral $\operatorname{li}(x)$
-- statement:
--   $\operatorname{li}(x)=\lim_{\varepsilon\to0^+}\operatorname{liPart}(x,\varepsilon)$, the limit taken along the right neighbourhood filter of $0$ (and a default value if the limit does not exist; it exists for every $x>1$).

import Mathlib
import Definitions.Def_LL_SchoenfeldLiS76_liPart

namespace LL_SchoenfeldLiS76

noncomputable section

open Real MeasureTheory Filter Topology Set intervalIntegral

noncomputable def liPV (x : ℝ) : ℝ := limUnder (𝓝[>] (0 : ℝ)) (liPart x)

end

end LL_SchoenfeldLiS76


