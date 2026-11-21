-- Prove2me | Definitions.Def_LL_Decomp587i_r1j9_lo
-- name    : LL_Decomp587i_r1j9_lo
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:37:36.429045+00:00
-- url     : https://prove2.me/theorems/454fe745-dd10-4314-af67-ed5074822075
-- title:
--   Lower endpoints of the box for $I_{2,9}$, Table 1 row two
-- statement:
--   The vector $(50/177,50/177,50/177)\in\mathbb Q^3$, indexed by $0,\dots,2$, of lower endpoints of the box for the term $I_{2,9}$ in Table 1 row two of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587i

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r1j9_lo : Fin 3 → ℚ := ![(50 / 177), (50 / 177), (50 / 177)]

end

end LL_Decomp587i


