-- Prove2me | Definitions.Def_LL_Burst9MatrixR1_ind
-- name    : LL_Burst9MatrixR1_ind
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:20:11.679605+00:00
-- url     : https://prove2.me/theorems/636a36bf-048a-401e-be07-73ad6a3d50ce
-- title:
--   Indicator of a closed interval
-- statement:
--   $\mathrm{ind}(a,b,t)$ is 1 when $a\le t\le b$, that is on the closed interval $[a,b]$, and 0 otherwise. In particular it is identically 0 when $a>b$.

import Mathlib

namespace LL_Burst9MatrixR1

noncomputable section

open Real Set MeasureTheory
open scoped Classical

def ind (a b t : ℝ) : ℝ := if a ≤ t ∧ t ≤ b then 1 else 0

end

end LL_Burst9MatrixR1


