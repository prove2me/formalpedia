-- Prove2me | Definitions.Def_LL_Decomp587k_r0j13_lo
-- name    : LL_Decomp587k_r0j13_lo
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:43:21.572338+00:00
-- url     : https://prove2.me/theorems/59af9da9-5026-4923-9a83-06025a474983
-- title:
--   Lower endpoints of the box for $I_{2,13}$, Table 1 row one
-- statement:
--   The vector $(50/227,100/353,10/29)\in\mathbb Q^3$, indexed by $0,\dots,2$, of lower endpoints of the box for the term $I_{2,13}$ in Table 1 row one of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587k

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r0j13_lo : Fin 3 → ℚ := ![(50 / 227), (100 / 353), (10 / 29)]

end

end LL_Decomp587k


