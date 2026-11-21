-- Prove2me | Definitions.Def_LL_Decomp587i_r1j9_hi
-- name    : LL_Decomp587i_r1j9_hi
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:37:46.404484+00:00
-- url     : https://prove2.me/theorems/b679716a-885c-468b-90cc-940d1719ac89
-- title:
--   Upper endpoints of the box for $I_{2,9}$, Table 1 row two
-- statement:
--   The vector $(100/243,100/243,100/243)\in\mathbb Q^3$, indexed by $0,\dots,2$, of upper endpoints of the box for the term $I_{2,9}$ in Table 1 row two of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587i

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r1j9_hi : Fin 3 → ℚ := ![(100 / 243), (100 / 243), (100 / 243)]

end

end LL_Decomp587i


