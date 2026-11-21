-- Prove2me | Definitions.Def_LL_Burst9MatrixR2_tableKernel
-- name    : LL_Burst9MatrixR2_tableKernel
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:37:49.841924+00:00
-- url     : https://prove2.me/theorems/d042ef11-2350-45f6-b275-7f9dd58426ff
-- title:
--   Kernel for each row of Wu's Section 7 matrix
-- statement:
--   For $i<4$ it is $\Xi_2$ with parameters tableParams $i$, and for $4\le i\le 8$ it is $\Xi_1$ with $s=\mathrm{grid}(i+1)\in\{2.6,\dots,3.0\}$ and $s'=\mathrm{tableSp}(i-4)$. Thus row $i$, counted from 0, is Wu's kernel $\Xi(t;s_{i+1})$ for row $i+1$.

import Mathlib
import Definitions.Def_LL_Burst9MatrixR2_Xi1
import Definitions.Def_LL_Burst9MatrixR2_Xi2
import Definitions.Def_LL_Burst9MatrixR2_tableParams
import Definitions.Def_LL_Burst9MatrixR2_grid
import Definitions.Def_LL_Burst9MatrixR2_tableSp

namespace LL_Burst9MatrixR2

noncomputable section

open Finset

def tableKernel (i : Fin 9) (t : ℝ) : ℝ :=
  if hi : i.val < 4 then Xi2 (tableParams ⟨i.val, hi⟩) t
  else Xi1 (grid ⟨i.val + 1, by omega⟩)
    (tableSp ⟨i.val - 4, by omega⟩) t

end

end LL_Burst9MatrixR2


