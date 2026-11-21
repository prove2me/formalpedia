-- Prove2me | Definitions.Def_LL_Decomp587i_r1j11_lo
-- name    : LL_Decomp587i_r1j11_lo
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:37:15.803929+00:00
-- url     : https://prove2.me/theorems/65e55b46-9187-4c0f-b8b4-02bbc51015bf
-- title:
--   Lower endpoints of the box for $I_{2,11}$, Table 1 row two
-- statement:
--   The vector $(50/177,25/72,25/72)\in\mathbb Q^3$, indexed by $0,\dots,2$, of lower endpoints of the box for the term $I_{2,11}$ in Table 1 row two of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587i

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r1j11_lo : Fin 3 → ℚ := ![(50 / 177), (25 / 72), (25 / 72)]

end

end LL_Decomp587i


