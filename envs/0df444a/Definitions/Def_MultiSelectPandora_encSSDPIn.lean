-- Prove2me | Definitions.Def_MultiSelectPandora_encSSDPIn
-- name    : MultiSelectPandora_encSSDPIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:15.290512+00:00
-- url     : https://prove2.me/theorems/71e2a0ea-7f57-4412-a3ef-2589009bcc1b
-- title:
--   Input encoding for tables
-- statement:
--   The encoded table followed by the encoded history.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Fact 3.3, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_encRawSSDP
import Definitions.Def_MultiSelectPandora_encHist
import Definitions.Def_OnlineCRS_Combine_Sym

open OnlineCRS.Combine

namespace MultiSelectPandora

/-- **Input encoding of the next-action machines of a table.** Auxiliary to Fact 3.3, p.8 (PDF p.9) of the Beyhaghi–Han–Luqman manuscript. -/
def encSSDPIn (p : RawSSDP × List (ℕ × ℕ)) : List Sym := encRawSSDP p.1 ++ encHist p.2

end MultiSelectPandora


