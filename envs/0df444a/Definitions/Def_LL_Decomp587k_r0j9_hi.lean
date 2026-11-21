-- Prove2me | Definitions.Def_LL_Decomp587k_r0j9_hi
-- name    : LL_Decomp587k_r0j9_hi
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:44:00.731178+00:00
-- url     : https://prove2.me/theorems/55611d7f-a822-437a-83c8-38b9c454b664
-- title:
--   Upper endpoints of the box for $I_{2,9}$, Table 1 row one
-- statement:
--   The vector $(25/61,25/61,25/61)\in\mathbb Q^3$, indexed by $0,\dots,2$, of upper endpoints of the box for the term $I_{2,9}$ in Table 1 row one of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587k

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r0j9_hi : Fin 3 → ℚ := ![(25 / 61), (25 / 61), (25 / 61)]

end

end LL_Decomp587k


