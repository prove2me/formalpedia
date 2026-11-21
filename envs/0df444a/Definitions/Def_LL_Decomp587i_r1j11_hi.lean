-- Prove2me | Definitions.Def_LL_Decomp587i_r1j11_hi
-- name    : LL_Decomp587i_r1j11_hi
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:37:25.730497+00:00
-- url     : https://prove2.me/theorems/ecaa507d-2183-4e0d-b312-64e74ebd847c
-- title:
--   Upper endpoints of the box for $I_{2,11}$, Table 1 row two
-- statement:
--   The vector $(25/72,100/243,100/243)\in\mathbb Q^3$, indexed by $0,\dots,2$, of upper endpoints of the box for the term $I_{2,11}$ in Table 1 row two of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587i

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r1j11_hi : Fin 3 → ℚ := ![(25 / 72), (100 / 243), (100 / 243)]

end

end LL_Decomp587i


