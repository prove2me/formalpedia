-- Prove2me | Definitions.Def_LL_Decomp587f_r3ElevenLo
-- name    : LL_Decomp587f_r3ElevenLo
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-18T01:01:59.610458+00:00
-- url     : https://prove2.me/theorems/671551a0-0fc3-479c-9968-91bdde5d040f
-- title:
--   Lower endpoints of the box for $I_{2,11}$
-- statement:
--   The vector $(25/89,100/291,100/291)\in\mathbb R^3$, indexed by $0,\dots,2$, of lower endpoints of the box for the term $I_{2,11}$ in Table 1 row four of Wu's Lemma 5.2.

import Mathlib

namespace LL_Decomp587f

noncomputable section

def r3ElevenLo : Fin 3 → ℝ := ![(25 / 89), (100 / 291), (100 / 291)]

end

end LL_Decomp587f


