-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_Admissible
-- name    : MultiSelectPandora_RawSSDP_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:17:37.965842+00:00
-- url     : https://prove2.me/theorems/aae82548-4d0f-4478-9299-36a398ebac24
-- title:
--   Admissible policies of a table
-- statement:
--   A policy of a table is admissible when it takes an available action at every reachable point within the horizon.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_RawSSDP_avail
import Definitions.Def_MultiSelectPandora_RawSSDP_Reach
import Definitions.Def_MultiSelectPandora_SSDPPolicy

namespace MultiSelectPandora

/-- **A policy of a table takes available actions.** Beyhaghi–Han–Luqman manuscript, §3.1, p.7 (PDF p.8). -/
def RawSSDP.Admissible (S : RawSSDP) (π : SSDPPolicy) : Prop :=
  ∀ h st R, S.Reach π h st R → h.length < S.T → S.avail R (π h) = true

end MultiSelectPandora


