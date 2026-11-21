-- Prove2me | Definitions.Def_LL_Burst9MatrixR3_grid
-- name    : LL_Burst9MatrixR3_grid
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:47:38.520872+00:00
-- url     : https://prove2.me/theorems/e5337d5b-c5d6-4a93-861c-6deb8d8e989e
-- title:
--   Wu's discretization points $s_0,\dots,s_9$
-- statement:
--   On Fin 10, $\mathrm{grid}(0)=1$ and $\mathrm{grid}(j)=2+(j+1)/10$ for $j=1,\dots,9$, giving Wu's points $s_0=1$, $s_1=2.2$, $s_2=2.3$, up to $s_9=3.0$. There is no point at $2.1$, so the first cell is $[1,2.2]$.

import Mathlib

namespace LL_Burst9MatrixR3

noncomputable section

open Real Set MeasureTheory
open scoped Classical

def grid (j : Fin 10) : ℝ := if j = 0 then 1 else 2 + (j.val + 1) / 10

end

end LL_Burst9MatrixR3


