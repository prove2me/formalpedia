-- Prove2me | Definitions.Def_LL_Decomp587i_r2j16_lo
-- name    : LL_Decomp587i_r2j16_lo
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:37:57.42462+00:00
-- url     : https://prove2.me/theorems/fa0af5ed-f4f8-4765-8504-84b4abfe83d9
-- title:
--   Lower endpoints of the box for $I_{2,16}$, Table 1 row three
-- statement:
--   The vector $(100/287,100/287,100/287,100/287)\in\mathbb Q^4$, indexed by $0,\dots,3$, of lower endpoints of the box for the term $I_{2,16}$ in Table 1 row three of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587i

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

def r2j16_lo : Fin 4 → ℚ := ![(100 / 287), (100 / 287), (100 / 287), (100 / 287)]

end

end LL_Decomp587i


