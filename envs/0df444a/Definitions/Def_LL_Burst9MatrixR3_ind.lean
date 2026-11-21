-- Prove2me | Definitions.Def_LL_Burst9MatrixR3_ind
-- name    : LL_Burst9MatrixR3_ind
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:44:49.113289+00:00
-- url     : https://prove2.me/theorems/f9075cd0-93af-461f-98c6-809d765608d9
-- title:
--   Indicator of a closed interval
-- statement:
--   $\mathrm{ind}(a,b,t)$ is 1 when $a\le t\le b$, that is on the closed interval $[a,b]$, and 0 otherwise. In particular it is identically 0 when $a>b$.

import Mathlib

namespace LL_Burst9MatrixR3

noncomputable section

open Real Set MeasureTheory
open scoped Classical

def ind (a b t : ℝ) : ℝ := if a ≤ t ∧ t ≤ b then 1 else 0

end

end LL_Burst9MatrixR3


