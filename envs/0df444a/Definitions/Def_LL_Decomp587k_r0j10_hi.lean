-- Prove2me | Definitions.Def_LL_Decomp587k_r0j10_hi
-- name    : LL_Decomp587k_r0j10_hi
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:42:43.692672+00:00
-- url     : https://prove2.me/theorems/e0aa5630-2f47-4e05-af5c-51d1a96fa2a1
-- title:
--   Upper endpoints of the box for $I_{2,10}$, Table 1 row one
-- statement:
--   The vector $(10/29,10/29,5/11)\in\mathbb Q^3$, indexed by $0,\dots,2$, of upper endpoints of the box for the term $I_{2,10}$ in Table 1 row one of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587k

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r0j10_hi : Fin 3 → ℚ := ![(10 / 29), (10 / 29), (5 / 11)]

end

end LL_Decomp587k


