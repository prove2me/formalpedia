-- Prove2me | Definitions.Def_LL_KLEndpointBudget_PrintedRow_deltaQ
-- name    : LL_KLEndpointBudget_PrintedRow_deltaQ
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-23T17:51:04.647135+00:00
-- url     : https://prove2.me/theorems/6f307911-711a-42ac-9b76-a31e2d4e75bc
-- title:
--   Row step $\delta$
-- statement:
--   For a row $r$, the rational number $\delta=\text{deltaUnits}/10^{12}$.

import Mathlib
import Definitions.Def_LL_KLEndpointBudget_PrintedRow

namespace LL_KLEndpointBudget

noncomputable section

open Real Set

def PrintedRow.deltaQ (r : PrintedRow) : ℚ := r.deltaUnits / 10 ^ 12

end

end LL_KLEndpointBudget


