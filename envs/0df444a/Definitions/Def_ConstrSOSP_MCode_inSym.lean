-- Prove2me | Definitions.Def_ConstrSOSP_MCode_inSym
-- name    : ConstrSOSP_MCode_inSym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:06.666309+00:00
-- url     : https://prove2.me/theorems/ea3b2a65-6939-498d-90d3-aa0f5ab706ec
-- title:
--   Writing a bit on the machine's tape
-- statement:
--   Input bits are written on the tape of a described machine with its two designated symbols: $0\mapsto$ the first, $1\mapsto$ the second.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib
import Definitions.Def_ConstrSOSP_MCode

namespace ConstrSOSP

/-- **Writing a bit on the tape of an `MCode` machine**: `false ↦ i0`, `true ↦ i1`
(arXiv:2604.02285, 2 Nov 2026, §4.1, p.17: inputs "described using b bits"). -/
def MCode.inSym (M : MCode) (b : Bool) : Fin M.g :=
  if b then M.i1 else M.i0

end ConstrSOSP


