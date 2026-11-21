-- Prove2me | Definitions.Def_LL_Burst9MatrixR1_tableSp
-- name    : LL_Burst9MatrixR1_tableSp
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:23:24.452458+00:00
-- url     : https://prove2.me/theorems/6b428b76-1842-494b-934f-ab02eab35f70
-- title:
--   Proposition 3 values of $s'$ in Wu's Table 1
-- statement:
--   The five values $s'=3.58, 3.47, 3.34, 3.19, 3.00$ of Wu's Table 1 rows $i=5,\dots,9$, indexed 0 to 4 on Fin 5 and paired with $s=2.6, 2.7, 2.8, 2.9, 3.0$.

import Mathlib

namespace LL_Burst9MatrixR1

noncomputable section

open Real Set MeasureTheory
open scoped Classical

def tableSp : Fin 5 → ℝ := ![3.58, 3.47, 3.34, 3.19, 3.00]

end

end LL_Burst9MatrixR1


