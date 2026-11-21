-- Prove2me | Definitions.Def_LL_Decomp587i_r1j10_hi
-- name    : LL_Decomp587i_r1j10_hi
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:37:01.436118+00:00
-- url     : https://prove2.me/theorems/bcd9b744-b22e-4620-a10c-9c81d41ddfe5
-- title:
--   Upper endpoints of the box for $I_{2,10}$, Table 1 row two
-- statement:
--   The vector $(25/72,25/72,10/23)\in\mathbb Q^3$, indexed by $0,\dots,2$, of upper endpoints of the box for the term $I_{2,10}$ in Table 1 row two of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587i

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r1j10_hi : Fin 3 → ℚ := ![(25 / 72), (25 / 72), (10 / 23)]

end

end LL_Decomp587i


