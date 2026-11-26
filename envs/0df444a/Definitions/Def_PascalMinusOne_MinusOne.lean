-- Prove2me | Definitions.Def_PascalMinusOne_MinusOne
-- name    : PascalMinusOne_MinusOne
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:17:20.181509+00:00
-- url     : https://prove2.me/theorems/e14108ae-1fa8-535e-8d47-56dc79c351c7
-- title:
--   Minus One
-- statement:
--   Definitions and structural lemmas for Minus One, from Upstream contributors (jfairfaxball-348/pascal-minus-one; see pinned Apache-2.0 LICENSE and README.md)'s pinned Pascal Minus-One GCD development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
set_option autoImplicit true
namespace PascalMinusOne
def minusOneExpectedValuation (m p A B : ℕ) : ℕ :=
  if A = 1 ∧ B = 1 ∧ p = m - 1 then 2
  else if A = 1 ∧ B = 1 ∧ m < p then 1
  else if (A = m ∧ B = 0) ∨ (A = 0 ∧ B = m) then 1
  else 0
end PascalMinusOne


