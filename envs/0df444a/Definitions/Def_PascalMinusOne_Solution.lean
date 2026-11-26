-- Prove2me | Definitions.Def_PascalMinusOne_Solution
-- name    : PascalMinusOne_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:20:05.085019+00:00
-- url     : https://prove2.me/theorems/cea99471-b6db-513a-8df8-6280867d14ef
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Upstream contributors (jfairfaxball-348/pascal-minus-one; see pinned Apache-2.0 LICENSE and README.md)'s pinned Pascal Minus-One GCD development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/Solution.lean

import Definitions.Def_PascalMinusOne
set_option autoImplicit true
namespace PascalMinusOnePalomar
def G (N m : ℕ) : ℕ :=
  ((Finset.range N).filter fun k ↦ 0 < k ∧ m ∣ k).gcd fun k ↦ N.choose k
def parityDigitSums : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | d :: ds =>
      let tail := parityDigitSums ds
      (d + tail.2, tail.1)
def evenDigitSum (p N : ℕ) : ℕ :=
  (parityDigitSums (Nat.digits p N)).1
def oddDigitSum (p N : ℕ) : ℕ :=
  (parityDigitSums (Nat.digits p N)).2
def minusOneExpectedValuation (m p A B : ℕ) : ℕ :=
  if A = 1 ∧ B = 1 ∧ p = m - 1 then 2
  else if A = 1 ∧ B = 1 ∧ m < p then 1
  else if (A = m ∧ B = 0) ∨ (A = 0 ∧ B = m) then 1
  else 0
end PascalMinusOnePalomar


