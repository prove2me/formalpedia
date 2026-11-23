-- Prove2me | Definitions.Def_LL_KLEndpointBudget_PrintedRow_threshold
-- name    : LL_KLEndpointBudget_PrintedRow_threshold
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-23T17:50:31.489976+00:00
-- url     : https://prove2.me/theorems/23a5b2de-1552-41cd-b109-88be55c86a75
-- title:
--   Row threshold $x_0$
-- statement:
--   For a row $r$, $x_0(r)=4\cdot10^{18}$ if its log index is $0$, and $x_0(r)=e^{k}$ if its log index is $k\neq0$.

import Mathlib
import Definitions.Def_LL_KLEndpointBudget_PrintedRow
import Definitions.Def_LL_KLEndpointBudget_evenBase

namespace LL_KLEndpointBudget

noncomputable section

open Real

noncomputable def PrintedRow.threshold (r : PrintedRow) : ℝ :=
  if r.logIndex = 0 then evenBase else Real.exp r.logIndex

end

end LL_KLEndpointBudget


