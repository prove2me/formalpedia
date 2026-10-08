-- Prove2me | Definitions.Def_GoldbachCertificate
-- name    : GoldbachCertificate
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-05T00:10:51.992763+00:00
-- url     : https://prove2.me/theorems/46c41fab-5a44-4873-bbbd-95fa968f50fa
-- title:
--   Finite Goldbach certificates with a shared prime dictionary
-- statement:
--   This interface represents a finite certificate for binary Goldbach. A finite dictionary tree contains candidate prime values, and an ordered list supplies a pair for every consecutive even integer beginning at $2a$. The Boolean checks validate dictionary primality, dictionary membership of both summands, the left-prime bound $p\le s$, and the exact total $p+q=2(a+i)$ in each row. No ordering assumption on the dictionary is trusted for soundness; a balanced ordered tree is a generator optimization.
--
--   The dictionary is shared across rows so a prime need not be certified independently for every representation. An untrusted program may generate the tree and pairs. The separate soundness theorem is needed to conclude a mathematical range assertion from successful checks. This definition itself supplies neither witnesses nor a proof of Goldbach.
-- source:
--   Checkable computational certificates for the finite Goldbach input in https://arxiv.org/abs/1201.6656; method, exact coverage and performance evidence in the statement.

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.Range

set_option autoImplicit false

namespace GoldbachCertificate

/-- A decidable primality test; certificate soundness is proved separately. -/
def primeCheck (p : ℕ) : Bool :=
  decide (2 ≤ p) &&
    (List.range (Nat.sqrt p + 1)).all (fun m => decide (m < 2 ∨ ¬ m ∣ p))

/-- A shared dictionary of prime values. Ordering improves lookup performance,
but is not required for soundness. -/
inductive PrimeTree where
  | empty
  | node (p : ℕ) (left right : PrimeTree)
  deriving DecidableEq

def PrimeTree.check : PrimeTree → Bool
  | .empty => true
  | .node p left right => primeCheck p && left.check && right.check

def PrimeTree.contains (n : ℕ) : PrimeTree → Bool
  | .empty => false
  | .node p left right =>
    if n = p then true else if n < p then left.contains n else right.contains n

/-- One literal prime pair for each consecutive even number, beginning at
`2 * first`. The left coordinate is bounded by `smallBound`. -/
def checkRows (first smallBound : ℕ) (tree : PrimeTree) : List (ℕ × ℕ) → Bool
  | [] => true
  | (p, q) :: rows =>
    tree.contains p && tree.contains q && decide (p ≤ smallBound) &&
      decide (p + q = 2 * first) && checkRows (first + 1) smallBound tree rows

end GoldbachCertificate


