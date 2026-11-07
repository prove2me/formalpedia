-- Prove2me | Definitions.Def_MultiSelectPandora_encHist
-- name    : MultiSelectPandora_encHist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:48.942618+00:00
-- url     : https://prove2.me/theorems/0381b229-2ef7-4939-9800-2f641e73d449
-- title:
--   Binary encoding of a raw history
-- statement:
--   A history is encoded as the list of its (box index, position) pairs, in binary.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Theorem 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_MultiSelectPandora_encList
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat

open OnlineCRS.Combine

namespace MultiSelectPandora

/-- **Binary encoding of a raw history.** Auxiliary to Theorem 1.1, p.2 (PDF p.3) of the Beyhaghi–Han–Luqman manuscript. -/
def encHist (h : List (ℕ × ℕ)) : List Sym := encList (fun e => encNat e.1 ++ [3] ++ encNat e.2) h

end MultiSelectPandora


