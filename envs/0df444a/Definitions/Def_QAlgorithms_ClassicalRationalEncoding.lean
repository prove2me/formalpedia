-- Prove2me | Definitions.Def_QAlgorithms_ClassicalRationalEncoding
-- name    : QAlgorithms_ClassicalRationalEncoding
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:51:32.130307+00:00
-- url     : https://prove2.me/theorems/72c8ff01-b797-4aa9-8897-1ea24e552f96
-- title:
--   Self-delimiting binary encoding of integers and rational numbers
-- statement:
--   An integer is encoded by its sign bit (one exactly when negative), followed by its absolute value in the self-delimiting binary code. A rational number is encoded by concatenating the integer code of its numerator and the natural-number code of its denominator. These are exactly the existing reviewed encInt and encRat interfaces, without changing numerical representation or input-size conventions.
-- source:
--   Reviewed shared binary encoding convention: QAlgorithms.LocalHamiltonian.encInt and encRat; exact declaration docstrings retained.

import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding

namespace QAlgorithms.LocalHamiltonian
open QAlgorithms.Complexity

/-- An integer: a sign bit, then the absolute value in self-delimiting binary. -/
def encInt (z : ℤ) : Str :=
  (if z < 0 then [true] else [false]) ++ encBin z.natAbs

/-- A rational number: numerator, then denominator. -/
def encRat (q : ℚ) : Str :=
  encInt q.num ++ encBin q.den

end QAlgorithms.LocalHamiltonian


