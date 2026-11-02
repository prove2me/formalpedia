-- Prove2me | Definitions.Def_TensorCoordinateCountdown
-- name    : TensorCoordinateCountdown
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T22:49:29.259611+00:00
-- url     : https://prove2.me/theorems/c6f80af3-642b-4ce8-93fa-dfd697173f40
-- title:
--   Reverse row-major coordinate countdown
-- statement:
--   A fixed four-stack program advances a pair of unary coordinates in reverse row-major order. It decrements the column when positive; otherwise it decrements the row and resets the column to a preserved maximum.

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_CookPvsNP_StackMacros

open CookPvsNP ProjSchedTW.Complexity

namespace TensorCoordinateCountdown

/-- The maximum column, current row, current column, and empty copy scratch. -/
def store (maximum row column : ℕ) : Fin 4 → List BSym :=
  fun k ↦ if k = 0 then List.replicate maximum .one
    else if k = 1 then List.replicate row .one
    else if k = 2 then List.replicate column .one else []

def columnNonempty (h : Fin 4 → Option BSym) : Bool := (h 2).isSome

def popAt (p : Fin 4) (_ : Fin 4 → Option BSym) (q : Fin 4) : StackAct BSym :=
  if q = p then .pop else .keep

/-- The next row-major pair in reverse order: decrease the column, or when
    it is zero, decrease the row and reset the column to its maximum. -/
def countdownProg : StackProg (Fin 4) BSym :=
  .branch columnNonempty (.act (popAt 2))
    (.seq (.act (popAt 1)) (copyProg 0 2 3))

end TensorCoordinateCountdown


