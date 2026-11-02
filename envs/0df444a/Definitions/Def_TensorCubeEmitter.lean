-- Prove2me | Definitions.Def_TensorCubeEmitter
-- name    : TensorCubeEmitter
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T21:49:49.511345+00:00
-- url     : https://prove2.me/theorems/f3af2f1a-99a4-4d47-88b6-c66bf7ff10c5
-- title:
--   Constant tensor coefficient selector
-- statement:
--   A fixed three-stack program reads two Boolean position flags and prepends the canonical rational encoding of the corresponding coefficient. A positive flag selects 1; otherwise a negative flag selects −1; otherwise the coefficient is 0. The flag stacks are not modified.

import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_TensorNP_Eigen_Defs

open CookPvsNP ProjSchedTW.Complexity

namespace TensorCubeEmitter

/-- Positive-position flag, negative-position flag, and output stack. -/
def store (positive negative output : List BSym) : Fin 3 → List BSym :=
  fun k ↦ if k = 0 then positive else if k = 1 then negative else output

def flagSym (b : Bool) : BSym := if b then .one else .zero

def hasPositive (h : Fin 3 → Option BSym) : Bool := h 0 == some .one
def hasNegative (h : Fin 3 → Option BSym) : Bool := h 1 == some .one

def emitProg : List BSym → StackProg (Fin 3) BSym
  | [] => .act (fun _ _ ↦ .keep)
  | a :: xs => .seq (emitProg xs) (.act (fun _ k ↦ if k = 2 then .push a else .keep))

/-- The priority form also defines a result for incompatible flags; genuine
    cube coordinates never set both flags. -/
def coefficient (positive negative : Bool) : ℚ :=
  if positive then 1 else if negative then -1 else 0

/-- Select one of the three exact rational encodings by the two flag heads. -/
def selectProg : StackProg (Fin 3) BSym :=
  .branch hasPositive (emitProg [.one,.sep,.one,.sep])
    (.branch hasNegative (emitProg [.minus,.one,.sep,.one,.sep])
      (emitProg [.sep,.one,.sep]))

end TensorCubeEmitter


