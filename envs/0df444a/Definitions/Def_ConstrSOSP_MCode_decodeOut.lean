-- Prove2me | Definitions.Def_ConstrSOSP_MCode_decodeOut
-- name    : ConstrSOSP_MCode_decodeOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:04.969855+00:00
-- url     : https://prove2.me/theorems/2485905d-e51b-4b11-8415-c3252711caf4
-- title:
--   Reading a bit string off the machine's tape
-- statement:
--   The tape contents of a halted machine are read back as bits through its two designated symbols; any other symbol (or a blank) makes the output unreadable.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib
import Definitions.Def_ConstrSOSP_MCode

namespace ConstrSOSP

/-- **Reading a bit string off the tape of an `MCode` machine**: the tape contents are read
symbol by symbol, `i0 ↦ false`, `i1 ↦ true`; any other symbol (or a blank) makes the output
unreadable (`none`). Used for the rational outputs of the white-box machines (arXiv:2604.02285,
2 Nov 2026, §4.1, p.17: "outputs rational values for f(x), ∇f(x) and ∇²f(x)"). -/
def MCode.decodeOut (M : MCode) (out : List (Option (Fin M.g))) : Option (List Bool) :=
  out.mapM (fun c => if c = some M.i1 then some true else if c = some M.i0 then some false
    else none)

end ConstrSOSP


