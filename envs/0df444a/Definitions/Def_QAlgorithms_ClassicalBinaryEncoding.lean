-- Prove2me | Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
-- name    : QAlgorithms_ClassicalBinaryEncoding
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:47:43.857693+00:00
-- url     : https://prove2.me/theorems/22f58fef-5568-42d2-b477-e329998acc04
-- title:
--   Self-delimiting binary encoding of natural numbers
-- statement:
--   Encode a natural number using its least-significant-bit-first binary digits. Replace each bit b by the two-bit pair (1,b), then append (0,0) as the terminator. The encoding of zero is just the terminator. This is the unchanged reviewed encBin interface used for inputs and outputs of classical integer-factoring algorithms.
-- source:
--   QAlgorithms.LocalHamiltonian.encBin, reviewed shared encoding convention; used by Servedio and Gortler, Quantum versus Classical Learnability, arXiv:quant-ph/0007036v1, section 5.

import Definitions.Def_QAlgorithms_ClassicalStringComputability

namespace QAlgorithms.LocalHamiltonian
open QAlgorithms.Complexity

/-- A natural number in self-delimiting binary: each bit `β` of `Nat.bits` (least significant
first) is written as the pair `1β`, and `00` ends the number. -/
def encBin (m : ℕ) : Str :=
  (Nat.bits m).flatMap (fun β => [true, β]) ++ [false, false]

end QAlgorithms.LocalHamiltonian


