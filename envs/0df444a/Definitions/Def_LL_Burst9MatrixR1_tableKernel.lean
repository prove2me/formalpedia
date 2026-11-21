-- Prove2me | Definitions.Def_LL_Burst9MatrixR1_tableKernel
-- name    : LL_Burst9MatrixR1_tableKernel
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:24:14.665741+00:00
-- url     : https://prove2.me/theorems/87c2f7cf-fd69-4d10-94f4-c416264de72f
-- title:
--   Kernel for each row of Wu's Section 7 matrix
-- statement:
--   For $i<4$ it is $\Xi_2$ with parameters tableParams $i$, and for $4\le i\le 8$ it is $\Xi_1$ with $s=\mathrm{grid}(i+1)\in\{2.6,\dots,3.0\}$ and $s'=\mathrm{tableSp}(i-4)$. Thus row $i$, counted from 0, is Wu's kernel $\Xi(t;s_{i+1})$ for row $i+1$.

import Mathlib
import Definitions.Def_LL_Burst9MatrixR1_Xi1
import Definitions.Def_LL_Burst9MatrixR1_Xi2
import Definitions.Def_LL_Burst9MatrixR1_tableParams
import Definitions.Def_LL_Burst9MatrixR1_grid
import Definitions.Def_LL_Burst9MatrixR1_tableSp

namespace LL_Burst9MatrixR1

noncomputable section

open Finset

def tableKernel (i : Fin 9) (t : ℝ) : ℝ :=
  if hi : i.val < 4 then Xi2 (tableParams ⟨i.val, hi⟩) t
  else Xi1 (grid ⟨i.val + 1, by omega⟩)
    (tableSp ⟨i.val - 4, by omega⟩) t

end

end LL_Burst9MatrixR1


