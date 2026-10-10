-- Prove2me | Definitions.Def_IntMul_BinarySubtractor
-- name    : IntMul_BinarySubtractor
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T18:41:29.555794+00:00
-- url     : https://prove2.me/theorems/d571de4b-18b7-49b8-b665-98fb9e365ddf
-- title:
--   Finite-state binary borrow and lexicographic comparison
-- statement:
--   Defines a Boolean subtractor digit and borrow bit, width-preserving little-endian subtraction and final borrow, and a three-state comparison scan for equal-width big-endian words. These are elementary finite arithmetic operations supporting a literal signed-subtraction tape machine. Correctness of the numeric difference and comparison is proved separately; no machine-cost assumption is included.
-- source:
--   Arithmetic foundations for the actual addition/subtraction primitive in the integer-multiplication κ campaign. The finite Boolean full-adder truth table is elementary. The canonical big-endian word encoding is the campaign’s IntMul_MultitapeModel: https://prove2.me/theorems/47ff1689-4e87-4af2-9406-674787e32429 .

import Definitions.Def_IntMul_BinaryAdder
import Mathlib.Data.Fintype.Basic

namespace IntMul.BinarySubtractor

/-- Binary difference digit for one borrow step. -/
def diffBit (a b borrow : Bool) : Bool := IntMul.BinaryAdder.sumBit a b borrow

/-- Borrow out of a single Boolean subtraction. -/
def borrowBit (a b borrow : Bool) : Bool := (!a && (b || borrow)) || (b && borrow)

/-- Width-preserving little-endian subtraction modulo the declared word width. -/
def subLittle : List Bool → List Bool → Bool → List Bool
  | a :: xs, b :: ys, c => diffBit a b c :: subLittle xs ys (borrowBit a b c)
  | _, _, _ => []

/-- Borrow left after processing all equal-width digits. -/
def finalBorrow : List Bool → List Bool → Bool → Bool
  | a :: xs, b :: ys, c => finalBorrow xs ys (borrowBit a b c)
  | _, _, c => c

inductive Comparison
  | lt | eq | gt
  deriving DecidableEq

instance : Fintype Comparison where
  elems := {.lt, .eq, .gt}
  complete := by intro q; cases q <;> simp

/-- Scan a pair of big-endian digits, retaining the first strict comparison. -/
def compareStep (q : Comparison) (a b : Bool) : Comparison :=
  match q with
  | .lt => .lt
  | .gt => .gt
  | .eq => if a = b then .eq else if b then .lt else .gt

/-- Finite-state big-endian lexicographic comparison. -/
def compareWords : List Bool → List Bool → Comparison → Comparison
  | a :: xs, b :: ys, q => compareWords xs ys (compareStep q a b)
  | _, _, q => q

end IntMul.BinarySubtractor


