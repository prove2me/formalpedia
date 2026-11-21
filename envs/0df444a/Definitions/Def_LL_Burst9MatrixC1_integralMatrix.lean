-- Prove2me | Definitions.Def_LL_Burst9MatrixC1_integralMatrix
-- name    : LL_Burst9MatrixC1_integralMatrix
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T05:00:36.470473+00:00
-- url     : https://prove2.me/theorems/12fcea69-952d-4860-9756-10471709b820
-- title:
--   Wu's Section 7 integral matrix $a_{i,j}$
-- statement:
--   Entry $(i,j)$, with both indices from 0, is the interval integral $\int_{\mathrm{grid}(j)}^{\mathrm{grid}(j+1)}\mathrm{tableKernel}(i,t)\,dt$, which is Wu's $a_{i+1,j+1}=\int_{s_j}^{s_{j+1}}\Xi(t;s_{i+1})\,dt$ from displays 7.1 and 7.2. As a Bochner integral it is 0 if the kernel is not integrable on that cell.

import Mathlib
import Definitions.Def_LL_Burst9MatrixC1_grid
import Definitions.Def_LL_Burst9MatrixC1_tableKernel

namespace LL_Burst9MatrixC1

noncomputable section

open Finset

def integralMatrix (i j : Fin 9) : ℝ :=
  ∫ t in grid ⟨j.val, by omega⟩..grid ⟨j.val + 1, by omega⟩,
    tableKernel i t

end

end LL_Burst9MatrixC1


