-- Prove2me | Definitions.Def_MultiSelectPandora_encRawSSDP
-- name    : MultiSelectPandora_encRawSSDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:15.780009+00:00
-- url     : https://prove2.me/theorems/abfb9900-2e6f-47f8-8ee3-3435caca5744
-- title:
--   Binary encoding of a table
-- statement:
--   A table is encoded as its numbers $L,T$, the initial state, the terminal rewards and the actions, with numbers and rationals in binary.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Fact 3.3, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_encList
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat

open OnlineCRS.Combine

namespace MultiSelectPandora

/-- **Binary encoding of a table.** Auxiliary to Fact 3.3, p.8 (PDF p.9) of the Beyhaghi–Han–Luqman manuscript. -/
def encRawSSDP (S : RawSSDP) : List Sym :=
  encNat S.L ++ [3] ++ encNat S.T ++ [3] ++ encNat S.init ++ [3] ++ encList encRat S.h ++
    encList (fun act =>
      (match act.1 with
        | none => [0, 3]
        | some g => [1, 3] ++ encNat g ++ [3]) ++
      encList (encList fun o => encRat o.1 ++ [3] ++ encRat o.2.1 ++ [3] ++ encNat o.2.2) act.2) S.actions

end MultiSelectPandora


