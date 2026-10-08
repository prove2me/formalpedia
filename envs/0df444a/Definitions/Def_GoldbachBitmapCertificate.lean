-- Prove2me | Definitions.Def_GoldbachBitmapCertificate
-- name    : GoldbachBitmapCertificate
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-05T00:37:22.745294+00:00
-- url     : https://prove2.me/theorems/4faef18f-e8d9-49c9-8b09-48356d39a1a0
-- title:
--   Compressed finite Goldbach certificates using shifted prime bitmaps
-- statement:
--   This definition represents odd dictionary primes as bits. A prime `q` contributes
--   the bit at index `q/2 - base` only when `q` is odd and `base ≤ q/2`. The guard is
--   essential: truncated natural subtraction must not turn a prime below the origin
--   into a spurious bit at zero.
--
--   For an odd left prime `p`, shifting the right-prime bitmap by `p/2 + 1` records
--   the even half-sums, since `(p+q)/2 = p/2 + q/2 + 1`. The union of these shifted
--   bitmaps is compared with a contiguous interval mask using bitwise intersection.
--   The prime dictionary and left-prime list are checked separately. A coverage
--   equality alone makes no claim about primality.
--
--   The interface supports nonzero origins, so a segment at a large numerical
--   location need not use an integer with that absolute number of bits. The
--   subsequent soundness theorem proves complete interval coverage from all three
--   checks. This definition contains no theorem claiming any unbounded Goldbach
--   result.
-- source:
--   Checkable computational certificates for the finite Goldbach input in https://arxiv.org/abs/1201.6656; method, exact coverage and performance evidence in the statement.

import Definitions.Def_GoldbachCertificate
import Mathlib.Data.Nat.Bitwise

set_option autoImplicit false

namespace GoldbachBitmapCertificate
open GoldbachCertificate

/-- Bit `i` records an odd prime with half-index `base + i`. -/
def primeBits (base : ℕ) : PrimeTree → ℕ
  | .empty => 0
  | .node p left right =>
    (if p % 2 = 1 ∧ base ≤ p / 2 then 1 <<< (p / 2 - base) else 0) |||
      primeBits base left ||| primeBits base right

/-- Every selected left summand is an odd checked prime within the bound. -/
def leftCheck (smallBound : ℕ) (tree : PrimeTree) (left : List ℕ) : Bool :=
  left.all (fun p => tree.contains p && decide (p % 2 = 1 ∧ p ≤ smallBound))

/-- For odd `p,q`, `(p+q)/2 = p/2 + q/2 + 1`. -/
def sumBits (right : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps => (right <<< (p / 2 + 1)) ||| sumBits right ps

def intervalMask (first count : ℕ) : ℕ := ((1 <<< count) - 1) <<< first

def covers (base first count : ℕ) (tree : PrimeTree) (left : List ℕ) : Bool :=
  decide ((sumBits (primeBits base tree) left &&& intervalMask first count) =
    intervalMask first count)

end GoldbachBitmapCertificate


