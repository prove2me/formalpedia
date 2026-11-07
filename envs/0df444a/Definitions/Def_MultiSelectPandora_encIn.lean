-- Prove2me | Definitions.Def_MultiSelectPandora_encIn
-- name    : MultiSelectPandora_encIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:06:41.295975+00:00
-- url     : https://prove2.me/theorems/5718a50f-1f12-4f9d-b3ed-f34fc93a6d5a
-- title:
--   Input encoding of the next-action machines
-- statement:
--   The input of a next-action machine is the encoded instance followed by the encoded history. On a reachable history each box appears once, so the input length is polynomial in the length of the instance alone. The verification file proves that this encoding is injective.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Theorem 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawInst
import Definitions.Def_MultiSelectPandora_encRawInst
import Definitions.Def_MultiSelectPandora_encHist
import Definitions.Def_OnlineCRS_Combine_Sym

open OnlineCRS.Combine

namespace MultiSelectPandora

/-- **Input encoding of the next-action machines**: the instance, then the history. Auxiliary to Theorem 1.1, p.2
(PDF p.3) of the Beyhaghi–Han–Luqman manuscript.

**Formalization Note.** On a reachable history each box appears once, so the input length is polynomial in the instance's. -/
def encIn (p : RawInst × List (ℕ × ℕ)) : List Sym := encRawInst p.1 ++ encHist p.2

end MultiSelectPandora


