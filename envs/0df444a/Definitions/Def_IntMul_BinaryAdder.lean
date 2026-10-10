-- Prove2me | Definitions.Def_IntMul_BinaryAdder
-- name    : IntMul_BinaryAdder
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T18:30:07.503776+00:00
-- url     : https://prove2.me/theorems/4d7f01af-c8f2-42fa-a29c-e23186d5cc2a
-- title:
--   Finite-state binary ripple-carry arithmetic
-- statement:
--   Defines the sum and carry bits of a Boolean full adder, least-significant-bit-first word value, and equal-width recursive ripple-carry addition including a final carry. These are pure arithmetic definitions supporting a literal fixed-tape addition machine. Their value, length, and exact campaign binary-encoding specifications are proved separately; this definition asserts no machine running-time assumption.
-- source:
--   Arithmetic foundations for the actual addition/subtraction primitive in the integer-multiplication κ campaign. The finite Boolean full-adder truth table is elementary. The canonical big-endian word encoding is the campaign’s IntMul_MultitapeModel: https://prove2.me/theorems/47ff1689-4e87-4af2-9406-674787e32429 .

import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.Basic

namespace IntMul.BinaryAdder

/-- Sum bit in one full-adder step. -/
def sumBit (a b c : Bool) : Bool := (a != b) != c

/-- Carry bit in one full-adder step. -/
def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- Value of a word written least significant bit first. -/
def littleVal : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * littleVal bs

/-- Ripple-carry addition on equal-width little-endian words. The result includes
the final carry bit. No specification is imposed on unequal operand widths. -/
def addLittle : List Bool → List Bool → Bool → List Bool
  | a :: as, b :: bs, c => sumBit a b c :: addLittle as bs (carryBit a b c)
  | _, _, c => [c]

end IntMul.BinaryAdder


