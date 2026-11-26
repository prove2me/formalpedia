-- Prove2me | Definitions.Def_PascalMinusOne_SmallModuli
-- name    : PascalMinusOne_SmallModuli
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:18:11.577732+00:00
-- url     : https://prove2.me/theorems/0e9cdd5d-dfbc-587f-a0a4-68a2d50ec749
-- title:
--   Small Moduli
-- statement:
--   Definitions and structural lemmas for Small Moduli, from Upstream contributors (jfairfaxball-348/pascal-minus-one; see pinned Apache-2.0 LICENSE and README.md)'s pinned Pascal Minus-One GCD development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SmallModuli.lean

import Definitions.Def_PascalMinusOne_PlusOne
import Definitions.Def_PascalMinusOne_Scaling
set_option autoImplicit true
namespace PascalMinusOne
def modulusThreeExpectedValuation (p N : ℕ) : ℕ :=
  if p = 3 then
    plusOneExpectedValuation 1 p (N / 3)
  else if p % 3 = 1 then
    plusOneExpectedValuation 3 p N
  else
    minusOneExpectedValuation 3 p (evenDigitSum p N) (oddDigitSum p N)
def modulusFourExpectedValuation (p N : ℕ) : ℕ :=
  if p = 2 then
    plusOneExpectedValuation 1 p (N / 4)
  else if p % 4 = 1 then
    plusOneExpectedValuation 4 p N
  else
    minusOneExpectedValuation 4 p (evenDigitSum p N) (oddDigitSum p N)
def modulusSixExpectedValuation (p N : ℕ) : ℕ :=
  if p = 2 then
    minusOneExpectedValuation 3 p
      (evenDigitSum p (N / 2)) (oddDigitSum p (N / 2))
  else if p = 3 then
    plusOneExpectedValuation 2 p (N / 3)
  else if p % 6 = 1 then
    plusOneExpectedValuation 6 p N
  else
    minusOneExpectedValuation 6 p (evenDigitSum p N) (oddDigitSum p N)
end PascalMinusOne


