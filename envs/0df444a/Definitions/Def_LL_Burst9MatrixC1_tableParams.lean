-- Prove2me | Definitions.Def_LL_Burst9MatrixC1_tableParams
-- name    : LL_Burst9MatrixC1_tableParams
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:57:55.479692+00:00
-- url     : https://prove2.me/theorems/6f3bda12-ab71-4b03-8937-a6a0b5601296
-- title:
--   Proposition 4 rows of Wu's Table 1
-- statement:
--   The four parameter rows of Wu's Table 1 for $i=1,\dots,4$, indexed 0 to 3 on Fin 4: $(s,s',\kappa_1,\kappa_2,\kappa_3)=(2.2,4.54,3.53,2.90,2.44)$, $(2.3,4.50,3.54,2.88,2.43)$, $(2.4,4.46,3.57,2.87,2.40)$, $(2.5,4.12,3.56,2.91,2.50)$, as exact real decimals.

import Mathlib
import Definitions.Def_LL_Burst9MatrixC1_Params

namespace LL_Burst9MatrixC1

noncomputable section

open Real Set MeasureTheory
open scoped Classical

def tableParams : Fin 4 → Params :=
  ![⟨2.2, 4.54, 3.53, 2.90, 2.44⟩, ⟨2.3, 4.50, 3.54, 2.88, 2.43⟩,
    ⟨2.4, 4.46, 3.57, 2.87, 2.40⟩, ⟨2.5, 4.12, 3.56, 2.91, 2.50⟩]

end

end LL_Burst9MatrixC1


