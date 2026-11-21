-- Prove2me | Definitions.Def_LL_Decomp587i_r2j16_hi
-- name    : LL_Decomp587i_r2j16_hi
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:38:09.649159+00:00
-- url     : https://prove2.me/theorems/2a790ad5-b161-4e50-a02e-dd8528929786
-- title:
--   Upper endpoints of the box for $I_{2,16}$, Table 1 row three
-- statement:
--   The vector $(5/12,5/12,5/12,5/12)\in\mathbb Q^4$, indexed by $0,\dots,3$, of upper endpoints of the box for the term $I_{2,16}$ in Table 1 row three of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587i

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r2j16_hi : Fin 4 → ℚ := ![(5 / 12), (5 / 12), (5 / 12), (5 / 12)]

end

end LL_Decomp587i


