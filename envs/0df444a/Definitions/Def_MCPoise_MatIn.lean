-- Prove2me | Definitions.Def_MCPoise_MatIn
-- name    : MCPoise_MatIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:06.899601+00:00
-- url     : https://prove2.me/theorems/45c9ec75-9e7f-4c4b-baa2-b74ed03f5b70
-- title:
--   Input and output of matrix rounding
-- statement:
--   The rational input of the matrix-rounding algorithm: a matrix as a list of rows, a vector $y$, and a bound $d$. The output is an integer vector. Both are written with length prefixes and rationals in binary.
--
--   **Formalization Note** Time on real input has no meaning for a Turing machine, so the algorithm is stated on rational data. The matrix built in the rounding step of the paper is rational.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem C.1, p.36

import Mathlib
import Definitions.Def_MCPoise_JLPOut
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat

namespace MCPoise

open OnlineCRS.Combine

/-- **Rational input of matrix rounding.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem C.1, p.36: "Let A be a real matrix and let y be a real vector. ... There is a polynomial-time algorithm".

`A` lists the rows. `d` is the column bound.

**Formalization Note.** Polynomial time has no meaning on real input to a Turing machine, so the algorithm of Theorem C.1 is stated on
rational data (the matrix built in Lemma 2.11 is rational); the existence claim is stated for real data separately. -/
structure MatIn where
  A : List (List ℚ)
  y : List ℚ
  d : ℚ

/-- The rational matrix of the input. Theorem C.1 asks each row to have length `y.length`. -/
def MatIn.mat (R : MatIn) : Matrix (Fin R.A.length) (Fin R.y.length) ℝ :=
  fun a q => (((R.A.get a).getD q.val 0 : ℚ) : ℝ)

/-- **Encoding of the input of matrix rounding.** Each list is length-prefixed, rationals in binary. Injective
(`Solutions/verification/MCPoise_sanity.lean`). -/
def encMatIn (R : MatIn) : List Sym :=
  EulerSparsify.joinW
    (ReserveLB.tokList (ReserveLB.tokList fun q : ℚ => [encRat q]) R.A ++
      ReserveLB.tokList (fun q : ℚ => [encRat q]) R.y ++ [encRat R.d])

/-- **Encoding of an integer vector,** the output of matrix rounding. Length first, then each integer with its sign bit. Injective. -/
def encInts (l : List ℤ) : List Sym :=
  EulerSparsify.joinW (ReserveLB.tokList (fun z : ℤ => [encInt z]) l)

end MCPoise


