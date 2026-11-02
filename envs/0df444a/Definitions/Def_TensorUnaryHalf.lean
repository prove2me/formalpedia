-- Prove2me | Definitions.Def_TensorUnaryHalf
-- name    : TensorUnaryHalf
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T21:32:10.106408+00:00
-- url     : https://prove2.me/theorems/571818b1-f484-44a6-94fe-b6e96c7706df
-- title:
--   Unary halving stack program
-- statement:
--   A three-stack program consumes a unary counter in pairs, accumulating its quotient and recording an unpaired token on a parity stack. It is intended as a component of a binary encoding machine.

import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding

open CookPvsNP ProjSchedTW.Complexity

namespace TensorUnaryHalf

/-- Input unary counter, output unary quotient, parity output. -/
def store (input quotient parity : List BSym) : Fin 3 → List BSym :=
  fun k ↦ if k=0 then input else if k=1 then quotient else parity

def nonempty (h : Fin 3 → Option BSym) : Bool := h 0 == some .one

def takeFirst (_ : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k=0 then .pop else .keep

def takePair (_ : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k=0 then .pop else if k=1 then .push .one else .keep

def markOdd (_ : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k=2 then .push .one else .keep

/-- Consume unary input two symbols at a time, counting pairs and marking an
    unpaired final symbol. All quotient and parity tails are preserved. -/
def halfProg : StackProg (Fin 3) BSym :=
  .loop nonempty (.seq (.act takeFirst) (.branch nonempty (.act takePair) (.act markOdd)))

end TensorUnaryHalf


