-- Prove2me | Definitions.Def_LL_Decomp587i_r1j10_lo
-- name    : LL_Decomp587i_r1j10_lo
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:36:50.980073+00:00
-- url     : https://prove2.me/theorems/ae802830-12a8-4f6c-be43-113f079d835f
-- title:
--   Lower endpoints of the box for $I_{2,10}$, Table 1 row two
-- statement:
--   The vector $(50/177,50/177,25/72)\in\mathbb Q^3$, indexed by $0,\dots,2$, of lower endpoints of the box for the term $I_{2,10}$ in Table 1 row two of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587i

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r1j10_lo : Fin 3 → ℚ := ![(50 / 177), (50 / 177), (25 / 72)]

end

end LL_Decomp587i


