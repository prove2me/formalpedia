-- Prove2me | Definitions.Def_LL_KLEndpointBudget_PrintedRow_aQ
-- name    : LL_KLEndpointBudget_PrintedRow_aQ
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-23T17:53:57.645908+00:00
-- url     : https://prove2.me/theorems/a1504c24-03b1-4658-8f65-b38d775de3dd
-- title:
--   Row cut $a$
-- statement:
--   For a row $r$, the rational number $a=\text{aUnits}/10^{4}$, the lower end of the printed interval for $a$.

import Mathlib
import Definitions.Def_LL_KLEndpointBudget_PrintedRow

namespace LL_KLEndpointBudget

noncomputable section

open Real Set

def PrintedRow.aQ (r : PrintedRow) : ℚ := r.aUnits / 10000

end

end LL_KLEndpointBudget


