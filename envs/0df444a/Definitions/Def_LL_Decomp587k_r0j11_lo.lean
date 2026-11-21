-- Prove2me | Definitions.Def_LL_Decomp587k_r0j11_lo
-- name    : LL_Decomp587k_r0j11_lo
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:42:56.025155+00:00
-- url     : https://prove2.me/theorems/0e4b1a80-ba9f-49f9-857d-b0c006682ae4
-- title:
--   Lower endpoints of the box for $I_{2,11}$, Table 1 row one
-- statement:
--   The vector $(100/353,10/29,10/29)\in\mathbb Q^3$, indexed by $0,\dots,2$, of lower endpoints of the box for the term $I_{2,11}$ in Table 1 row one of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587k

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r0j11_lo : Fin 3 → ℚ := ![(100 / 353), (10 / 29), (10 / 29)]

end

end LL_Decomp587k


