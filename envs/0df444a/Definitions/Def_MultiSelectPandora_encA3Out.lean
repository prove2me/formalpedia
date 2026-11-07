-- Prove2me | Definitions.Def_MultiSelectPandora_encA3Out
-- name    : MultiSelectPandora_encA3Out
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:31.34452+00:00
-- url     : https://prove2.me/theorems/9eaeb5ab-196d-4d9b-bfd3-78c49a568ea6
-- title:
--   Binary encoding of the output of Claim A.3
-- statement:
--   The binary encoding of the objects of Claim A.3, field by field.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Claim A.3, p.31 (PDF p.32)

import Mathlib
import Definitions.Def_MultiSelectPandora_A3Output
import Definitions.Def_MultiSelectPandora_encRawSSDP
import Definitions.Def_MultiSelectPandora_encList
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encRat

open OnlineCRS.Combine

namespace MultiSelectPandora

/-- **Binary encoding of the output of Claim A.3.** Auxiliary to Claim A.3, p.31 (PDF p.32) of the Beyhaghi–Han–Luqman manuscript. -/
def encA3Out (o : A3Output) : List Sym :=
  encList encRat o.sigma ++ encRat o.W ++ [3] ++ encRat o.OPTC ++ [3] ++ encRat o.theta ++ [3] ++ encList encRat o.grid ++
    encList (encList encRat) o.wVals ++ encList (encList encRat) o.xVals ++ encRawSSDP o.table

end MultiSelectPandora


