-- Prove2me | Definitions.Def_MultiSelectPandora_encList
-- name    : MultiSelectPandora_encList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:39.81922+00:00
-- url     : https://prove2.me/theorems/0f2240b3-7193-40cc-af42-f791e8b3418d
-- title:
--   Binary encoding of a list
-- statement:
--   A list is encoded as its length in binary, a separator, and each entry followed by the separator. The verification file proves that this encoding is a prefix code when the entries' encodings are.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Theorem 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat

open OnlineCRS.Combine

namespace MultiSelectPandora

/-- **Binary encoding of a list**: its length, the separator `3`, then each entry followed by `3`.
Auxiliary to Theorem 1.1, p.2 (PDF p.3) of the Beyhaghi–Han–Luqman manuscript.

**Formalization Note.** Numbers are binary (`OnlineCRS.Combine.encNat`), never unary. The input size of the machines is
therefore the usual bit length. -/
def encList {α : Type} (f : α → List Sym) (l : List α) : List Sym :=
  encNat l.length ++ [3] ++ l.flatMap fun a => f a ++ [3]

end MultiSelectPandora


