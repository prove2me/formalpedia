-- Prove2me | Definitions.Def_IntMul_BinarySchoolbook
-- name    : IntMul_BinarySchoolbook
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T19:56:06.818572+00:00
-- url     : https://prove2.me/theorems/1b64cc5b-7521-41d5-963f-e1ea2cb6837f
-- title:
--   Fixed-width binary shift-and-add multiplication words
-- statement:
--   Defines explicit fixed-width little-endian shift, discarded high shift carry, fixed-width ripple addition and discarded high add carry, an MSB-first multiplier-bit Horner step, and its fold. The product word has exactly twice the first operand width and is returned big-endian with all leading zeros. These are finite-word operations; a literal multitape implementation and its quadratic running-time proof are separate obligations.
-- source:
--   Classical shift-and-add algorithm used in the existing IntMul.TM.schoolbook milestone (86109c88-e1e4-410a-a312-0a5f005a04cf). Original fixed-width word and machine interface formalization, Written by Codex.

import Definitions.Def_IntMul_BinaryAdder

namespace IntMul.BinarySchoolbook

/-- Shift toward larger significance while retaining the declared width.
The incoming low-order bit is `previous`. Words are little-endian. -/
def shiftCarry (previous : Bool) : List Bool → List Bool
  | [] => []
  | b :: bs => previous :: shiftCarry b bs

/-- The bit discarded at the high-order end of a fixed-width shift. -/
def highCarry (previous : Bool) : List Bool → Bool
  | [] => previous
  | b :: bs => highCarry b bs

/-- Fixed-width ripple addition. The final high carry is discarded. -/
def addFixed : List Bool → List Bool → Bool → List Bool
  | [], _, _ => []
  | _, [], _ => []
  | a :: xs, b :: ys, c =>
      BinaryAdder.sumBit a b c :: addFixed xs ys (BinaryAdder.carryBit a b c)

def lastCarry : List Bool → List Bool → Bool → Bool
  | [], _, c => c
  | _, [], c => c
  | a :: xs, b :: ys, c => lastCarry xs ys (BinaryAdder.carryBit a b c)

/-- A most-significant-first multiplier bit shifts the running product and,
when set, adds the padded first operand. -/
def advanceWord (x p : List Bool) (b : Bool) : List Bool :=
  if b then addFixed (shiftCarry false p) x false else shiftCarry false p

/-- Horner's shift-and-add multiplication, with a fixed-width accumulator. -/
def foldWord (x : List Bool) (y : List Bool) (p : List Bool) : List Bool :=
  y.foldl (advanceWord x) p

/-- Big-endian, exactly twice-input-width shift-and-add output. -/
def productWord (x y : List Bool) : List Bool :=
  (foldWord ((List.replicate x.length false ++ x).reverse) y
    (List.replicate (2 * x.length) false)).reverse

end IntMul.BinarySchoolbook


