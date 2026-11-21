-- Prove2me | Definitions.Def_LL_Decomp587k_r0j11_hi
-- name    : LL_Decomp587k_r0j11_hi
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:43:09.343098+00:00
-- url     : https://prove2.me/theorems/869d5217-6f8b-4576-8ff9-526dcf417165
-- title:
--   Upper endpoints of the box for $I_{2,11}$, Table 1 row one
-- statement:
--   The vector $(10/29,25/61,25/61)\in\mathbb Q^3$, indexed by $0,\dots,2$, of upper endpoints of the box for the term $I_{2,11}$ in Table 1 row one of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587k

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r0j11_hi : Fin 3 → ℚ := ![(10 / 29), (25 / 61), (25 / 61)]

end

end LL_Decomp587k


