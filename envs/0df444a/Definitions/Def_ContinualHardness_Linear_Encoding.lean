-- Prove2me | Definitions.Def_ContinualHardness_Linear_Encoding
-- name    : ContinualHardness_Linear_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:11:12.257089+00:00
-- url     : https://prove2.me/theorems/683af477-1353-4639-9ca2-bc8cfef2b543
-- title:
--   Self-delimiting binary codes of naturals, integers, rationals and lists
-- statement:
--   All instances are written as bit strings (`List Bool`). A natural number $n$ is written by its binary digits $b_1b_2\cdots b_k$ (least significant first), each digit preceded by a marker bit $1$, and the code ends with a single $0$:
--   $$\mathrm{enc}(n)=1\,b_1\,1\,b_2\cdots 1\,b_k\,0,$$
--   of length $2k+1=O(\log n)$; it is self-delimiting, so codes can be concatenated without separators (`encNat`). An integer is a sign bit (1 for negative) followed by the code of its absolute value (`encInt`); a rational number in lowest terms is the code of its numerator followed by the code of its positive denominator (`encRat`); a list is its length followed by the codes of its entries (`encList`). These are standard binary encodings: the code of an object is injective and of length polynomial in the bit size of the object.
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), pp. 4, 7 (instances of Theorem 3.1 are finite datasets given as input; PDF pp. 5, 8)

import Mathlib

namespace ContinualHardness.Linear

/-! # A standard self-delimiting binary encoding of naturals, integers, rationals and lists

Every code is a `List Bool`. A natural number is written by its binary digits
(least significant first, `Nat.bits`), each digit preceded by the marker bit `true`, and the code
ends with a single `false`; so `encNat n` has length `2 · (bit length of n) + 1` and can be read
off a longer string without a separator. -/

/-- Self-delimiting binary code of a natural number: each binary digit `b` (least significant
first) becomes `true, b`, and the code ends with `false`. -/
def encNat (n : ℕ) : List Bool :=
  (Nat.bits n).flatMap (fun b => [true, b]) ++ [false]

/-- Code of an integer: a sign bit (`true` for negative) followed by the code of its absolute
value. -/
def encInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encNat z.natAbs

/-- Code of a rational number in lowest terms: the code of its numerator followed by the code of
its (positive) denominator. -/
def encRat (q : ℚ) : List Bool :=
  encInt q.num ++ encNat q.den

/-- Code of a list: its length, then the codes of its entries in order. -/
def encList {α : Type} (e : α → List Bool) (l : List α) : List Bool :=
  encNat l.length ++ l.flatMap e

end ContinualHardness.Linear


