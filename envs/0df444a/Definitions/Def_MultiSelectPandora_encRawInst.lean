-- Prove2me | Definitions.Def_MultiSelectPandora_encRawInst
-- name    : MultiSelectPandora_encRawInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:12.106375+00:00
-- url     : https://prove2.me/theorems/3179104d-19e0-4763-a921-8c6764f8a495
-- title:
--   Binary encoding of a rational instance
-- statement:
--   A rational instance is encoded box by box: the cost, then the list of (value, probability) pairs. Rationals are written as reduced numerator and denominator in binary. The length of this word is the input size of the machines.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Theorem 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawInst
import Definitions.Def_MultiSelectPandora_encList
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encRat

open OnlineCRS.Combine

namespace MultiSelectPandora

/-- **Binary encoding of a rational instance.** Auxiliary to Theorem 1.1, p.2 (PDF p.3) of the Beyhaghi–Han–Luqman
manuscript. Rationals are reduced numerator/denominator (`OnlineCRS.Combine.encRat`). -/
def encRawInst (I : RawInst) : List Sym :=
  encList (fun b => encRat b.1 ++ [3] ++ encList (fun p => encRat p.1 ++ [3] ++ encRat p.2) b.2) I

end MultiSelectPandora


