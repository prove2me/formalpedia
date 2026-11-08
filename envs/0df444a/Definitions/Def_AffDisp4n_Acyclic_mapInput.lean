-- Prove2me | Definitions.Def_AffDisp4n_Acyclic_mapInput
-- name    : AffDisp4n_Acyclic_mapInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:19.090053+00:00
-- url     : https://prove2.me/theorems/a3d45b39-5413-41ca-80ad-07abdf4b7cee
-- title:
--   Renaming the inputs of a straight-line circuit
-- statement:
--   For a map $e : V \to V'$, renaming the inputs of a straight-line circuit along $e$ makes every gate input and the output that read the input $v$ read $e(v)$ instead. The operations, the wiring between gates, and the output literal are unchanged.
--
--   It is used to exchange the roles of a parameter and an auxiliary variable in (AR): this "does not change any equation or gate of the circuit" (§3.2, p.21).
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.6, pp.18–19; §3.2, p.21

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic

namespace AffDisp4n

/-- **Renaming the inputs** of a straight-line circuit along `e : V → V'`. Every gate input, and the
output, that read the input `v` read `e v` instead. Operations and the wiring between gates are
unchanged (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.6 "Preserving the representation", pp.18–19, and §3.2, p.21: exchanging a parameter
and an auxiliary variable "does not change any equation or gate of the circuit"). -/
def Acyclic.mapInput {V V' : Type} (C : Acyclic V) (e : V → V') : Acyclic V' where
  size := C.size
  op := C.op
  in₁ := fun g => (C.in₁ g).map e
  in₂ := fun g => (C.in₂ g).map e
  out := C.out.map e
  outNeg := C.outNeg

end AffDisp4n


