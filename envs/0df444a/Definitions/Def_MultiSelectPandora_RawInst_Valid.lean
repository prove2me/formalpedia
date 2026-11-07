-- Prove2me | Definitions.Def_MultiSelectPandora_RawInst_Valid
-- name    : MultiSelectPandora_RawInst_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:45.336564+00:00
-- url     : https://prove2.me/theorems/0db0eb90-2991-4d1d-b1f3-044cf29a018c
-- title:
--   Validity of a rational instance
-- statement:
--   A rational instance is valid when its real instance is.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_RawInst_toInst

namespace MultiSelectPandora

/-- **Validity of a rational instance**: its real instance is valid (§2.1, p.5, PDF p.6, Beyhaghi–Han–Luqman manuscript). -/
def RawInst.Valid (I : RawInst) : Prop := I.toInst.Valid

end MultiSelectPandora


