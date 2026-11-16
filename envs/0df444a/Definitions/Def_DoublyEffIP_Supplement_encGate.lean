-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_encGate
-- name    : DoublyEffIP_Supplement_encGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:26:57.614163+00:00
-- url     : https://prove2.me/theorems/d0eae4f4-626e-4136-84f6-75117e678260
-- title:
--   The bit code of a gate
-- statement:
--   The **code of a gate** is a tag $0,1,2,3$ (for ADD, MULT, constant, generator) in self-delimited binary, followed by the two wire numbers in self-delimited binary, or by the constant's bit.
--
--   Every code starts with a self-delimited tag, so the code determines the gate. Gate codes make up the description of a circuit that a uniform machine outputs.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9, Definition 3 (the full description of the circuit)

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_Gate
import Definitions.Def_DoublyEffIP_encBin

set_option autoImplicit false

namespace DoublyEffIP.Supplement

/-- **The bit code of a gate** — part of "the full description of the circuit" output by the
generating machine in Definition 3 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9.

A tag `0`, `1`, `2`, `3` for `add`, `mul`, `const`, `gen` in self-delimited binary, followed by the
two wire numbers (in self-delimited binary) or the constant's bit.

**Formalization Note.** Every code starts with a self-delimited tag, so a code determines its gate.
-/
def encGate : Gate → List Bool
  | .add i j => encBin 0 ++ encBin i ++ encBin j
  | .mul i j => encBin 1 ++ encBin i ++ encBin j
  | .const b => encBin 2 ++ [b]
  | .gen => encBin 3

end DoublyEffIP.Supplement


