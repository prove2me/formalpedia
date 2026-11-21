-- Prove2me | Definitions.Def_LL_Decomp587k_r0j13_hi
-- name    : LL_Decomp587k_r0j13_hi
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:43:33.537991+00:00
-- url     : https://prove2.me/theorems/f5c0c42a-9102-48b7-9898-700d331921d6
-- title:
--   Upper endpoints of the box for $I_{2,13}$, Table 1 row one
-- statement:
--   The vector $(100/353,10/29,5/11)\in\mathbb Q^3$, indexed by $0,\dots,2$, of upper endpoints of the box for the term $I_{2,13}$ in Table 1 row one of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587k

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r0j13_hi : Fin 3 → ℚ := ![(100 / 353), (10 / 29), (5 / 11)]

end

end LL_Decomp587k


