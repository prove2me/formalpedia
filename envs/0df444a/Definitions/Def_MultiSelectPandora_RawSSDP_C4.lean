-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_C4
-- name    : MultiSelectPandora_RawSSDP_C4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:18:47.386627+00:00
-- url     : https://prove2.me/theorems/57038cb1-6a86-44b8-8f69-8ad3c386425e
-- title:
--   Condition (C4)
-- statement:
--   Condition (C4) with constant $D$: $\mathrm{MAX}\le D\cdot\mathrm{OPT}$, that is $\mathrm{MAX}=O(\mathrm{OPT})$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.2, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_RawSSDP_OPT
import Definitions.Def_MultiSelectPandora_RawSSDP_MAX

namespace MultiSelectPandora

/-- **Condition (C4) with constant `D`**: `MAX ≤ D · OPT`, that is `MAX = O(OPT)`. Beyhaghi–Han–Luqman manuscript, Definition 3.2, p.8 (PDF p.9). -/
def RawSSDP.C4 (S : RawSSDP) (D : ℝ) : Prop := S.MAX ≤ D * S.OPT

end MultiSelectPandora


