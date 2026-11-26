-- Prove2me | Definitions.Def_PascalMinusOne_PlusOne
-- name    : PascalMinusOne_PlusOne
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:17:40.277877+00:00
-- url     : https://prove2.me/theorems/c5657e89-1b08-5c47-a618-04cd7e63d226
-- title:
--   Plus One
-- statement:
--   Definitions and structural lemmas for Plus One, from Upstream contributors (jfairfaxball-348/pascal-minus-one; see pinned Apache-2.0 LICENSE and README.md)'s pinned Pascal Minus-One GCD development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/PlusOne.lean

import Definitions.Def_PascalMinusOne_MinusOne
import Mathlib.Data.Nat.Digits.Lemmas
set_option autoImplicit true
namespace PascalMinusOne
def plusOneExpectedValuation (m p N : ℕ) : ℕ :=
  if (Nat.digits p N).sum = m then 1 else 0
end PascalMinusOne


