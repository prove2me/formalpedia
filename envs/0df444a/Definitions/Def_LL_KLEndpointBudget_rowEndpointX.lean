-- Prove2me | Definitions.Def_LL_KLEndpointBudget_rowEndpointX
-- name    : LL_KLEndpointBudget_rowEndpointX
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-23T17:52:29.765868+00:00
-- url     : https://prove2.me/theorems/3f5b4608-6044-443b-8a99-bfab50fb5d45
-- title:
--   Least admissible point $X=x_0/(e^{u}(1+\delta))$
-- statement:
--   For a row $r$, the real number $X=x_0/\bigl(e^{u}(1+\delta)\bigr)$.

import Mathlib
import Definitions.Def_LL_KLEndpointBudget_PrintedRow
import Definitions.Def_LL_KLEndpointBudget_PrintedRow_threshold
import Definitions.Def_LL_KLEndpointBudget_PrintedRow_deltaQ
import Definitions.Def_LL_KLEndpointBudget_PrintedRow_uQ

namespace LL_KLEndpointBudget

noncomputable section

open Real Set MeasureTheory

noncomputable def rowEndpointX (r : PrintedRow) : ℝ :=
  r.threshold / (Real.exp r.uQ * (1 + (r.deltaQ : ℝ)))

end

end LL_KLEndpointBudget


