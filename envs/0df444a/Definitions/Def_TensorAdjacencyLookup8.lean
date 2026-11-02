-- Prove2me | Definitions.Def_TensorAdjacencyLookup8
-- name    : TensorAdjacencyLookup8
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T22:02:41.943486+00:00
-- url     : https://prove2.me/theorems/ff4b4acd-d1f2-428f-948d-392a68e6c2a3
-- title:
--   Stack-program lookup in a row-major matrix
-- statement:
--   A fixed eight-stack program copies a row-major matrix, forms a unary row-major offset from unary row, column and dimension, advances to that position, emits the selected symbol, and clears its scratch stacks. The matrix and indices are retained.

import Mathlib
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_CookPvsNP_StackRepeat
import Definitions.Def_ProjSchedTW_Complexity_Encoding

open CookPvsNP ProjSchedTW.Complexity
namespace TensorAdjacencyLookup8

/-- Matrix, dimension, row, column, output, offset, temporary data, scratch. -/
def store (data dim row col output offset tmp scratch : List BSym) : Fin 8 → List BSym :=
  fun k ↦ if k=0 then data else if k=1 then dim else if k=2 then row else if k=3 then col
    else if k=4 then output else if k=5 then offset else if k=6 then tmp else scratch

/-- The repeat-copy ports represent dimension, product, loop count and scratch. -/
def multiplyPorts : Fin 4 ↪ Fin 8 := ⟨![1,5,6,7], by decide⟩

def hasOffsetAndData (h : Fin 8 → Option BSym) : Bool :=
  (h 5 == some .one) && (h 6).isSome

def skipAction (_ : Fin 8 → Option BSym) (k : Fin 8) : StackAct BSym :=
  if k=5 ∨ k=6 then .pop else .keep

def readAction (h : Fin 8 → Option BSym) (k : Fin 8) : StackAct BSym :=
  if k=4 then match h 6 with | some a => .push a | none => .keep else .keep

/-- Compute i*v+j in unary, copy the matrix, skip to the indexed position,
    emit its symbol, and clear the temporary matrix copy. -/
def lookupProg : StackProg (Fin 8) BSym :=
  .seq (copyProg 2 6 7)
    (.seq (repeatCopyProg multiplyPorts)
      (.seq (copyProg 3 5 6)
        (.seq (copyProg 0 6 7)
          (.seq (.loop hasOffsetAndData (.act skipAction))
            (.seq (.act readAction) (clearProg 6))))))

end TensorAdjacencyLookup8


