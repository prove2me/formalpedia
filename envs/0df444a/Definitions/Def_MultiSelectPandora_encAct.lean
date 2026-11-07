-- Prove2me | Definitions.Def_MultiSelectPandora_encAct
-- name    : MultiSelectPandora_encAct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:04:27.859405+00:00
-- url     : https://prove2.me/theorems/12ffe732-df15-4a10-981b-d203567f6906
-- title:
--   Output encoding of the next-action machines
-- statement:
--   An output is encoded as a tag followed by the box index in binary, or by the list of selected indices. The verification file proves that this encoding is injective.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Theorem 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawAct
import Definitions.Def_MultiSelectPandora_encList
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat

open OnlineCRS.Combine

namespace MultiSelectPandora

/-- **Output encoding of the next-action machines.** Auxiliary to Theorem 1.1, p.2 (PDF p.3) of the
Beyhaghi–Han–Luqman manuscript. -/
def encAct : RawAct → List Sym
  | .openBox i => [0, 3] ++ encNat i
  | .stop S => [1, 3] ++ encList encNat S

end MultiSelectPandora


