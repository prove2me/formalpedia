-- Prove2me | Definitions.Def_LL_Burst9MatrixR3_tableKernel
-- name    : LL_Burst9MatrixR3_tableKernel
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:48:47.680561+00:00
-- url     : https://prove2.me/theorems/d3034319-bd28-44da-8f77-c4e88805cf8c
-- title:
--   Kernel for each row of Wu's Section 7 matrix
-- statement:
--   For $i<4$ it is $\Xi_2$ with parameters tableParams $i$, and for $4\le i\le 8$ it is $\Xi_1$ with $s=\mathrm{grid}(i+1)\in\{2.6,\dots,3.0\}$ and $s'=\mathrm{tableSp}(i-4)$. Thus row $i$, counted from 0, is Wu's kernel $\Xi(t;s_{i+1})$ for row $i+1$.

import Mathlib
import Definitions.Def_LL_Burst9MatrixR3_Xi1
import Definitions.Def_LL_Burst9MatrixR3_Xi2
import Definitions.Def_LL_Burst9MatrixR3_tableParams
import Definitions.Def_LL_Burst9MatrixR3_grid
import Definitions.Def_LL_Burst9MatrixR3_tableSp

namespace LL_Burst9MatrixR3

noncomputable section

open Finset

def tableKernel (i : Fin 9) (t : ℝ) : ℝ :=
  if hi : i.val < 4 then Xi2 (tableParams ⟨i.val, hi⟩) t
  else Xi1 (grid ⟨i.val + 1, by omega⟩)
    (tableSp ⟨i.val - 4, by omega⟩) t

end

end LL_Burst9MatrixR3


