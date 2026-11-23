-- Prove2me | Definitions.Def_LL_KLEndpointBudget_PrintedRow_uQ
-- name    : LL_KLEndpointBudget_PrintedRow_uQ
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-23T17:51:42.900876+00:00
-- url     : https://prove2.me/theorems/0f4c78c8-1ee0-429c-812e-8ba77749e246
-- title:
--   Row parameter $u=\delta/m$
-- statement:
--   For a row $r$, the rational number $u=\delta/m$ (with $u=0$ if $m=0$).

import Mathlib
import Definitions.Def_LL_KLEndpointBudget_PrintedRow
import Definitions.Def_LL_KLEndpointBudget_PrintedRow_deltaQ

namespace LL_KLEndpointBudget

noncomputable section

open Real Set

def PrintedRow.uQ (r : PrintedRow) : ℚ := r.deltaQ / r.m

end

end LL_KLEndpointBudget


