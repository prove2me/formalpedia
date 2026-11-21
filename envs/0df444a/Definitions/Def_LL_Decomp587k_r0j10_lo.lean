-- Prove2me | Definitions.Def_LL_Decomp587k_r0j10_lo
-- name    : LL_Decomp587k_r0j10_lo
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:42:31.053888+00:00
-- url     : https://prove2.me/theorems/95286662-db4c-4929-ba59-1ea07a7ca837
-- title:
--   Lower endpoints of the box for $I_{2,10}$, Table 1 row one
-- statement:
--   The vector $(100/353,100/353,10/29)\in\mathbb Q^3$, indexed by $0,\dots,2$, of lower endpoints of the box for the term $I_{2,10}$ in Table 1 row one of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587k

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r0j10_lo : Fin 3 → ℚ := ![(100 / 353), (100 / 353), (10 / 29)]

end

end LL_Decomp587k


