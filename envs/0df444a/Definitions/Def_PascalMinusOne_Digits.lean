-- Prove2me | Definitions.Def_PascalMinusOne_Digits
-- name    : PascalMinusOne_Digits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:16:44.686461+00:00
-- url     : https://prove2.me/theorems/9340e484-f19f-4c77-aa52-280cd085e08d
-- title:
--   Digits
-- statement:
--   Definitions and structural lemmas for Digits, from Upstream contributors (jfairfaxball-348/pascal-minus-one; see pinned Apache-2.0 LICENSE and README.md)'s pinned Pascal Minus-One GCD development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Digits.lean

import Mathlib.Data.Nat.Digits.Lemmas
set_option autoImplicit true
namespace PascalMinusOne
def parityDigitSums : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | d :: ds =>
      let tail := parityDigitSums ds
      (d + tail.2, tail.1)
def evenDigitSum (p N : ℕ) : ℕ :=
  (parityDigitSums (Nat.digits p N)).1
def oddDigitSum (p N : ℕ) : ℕ :=
  (parityDigitSums (Nat.digits p N)).2
def digitAt (p N i : ℕ) : ℕ :=
  N / p ^ i % p
def Occupied (p N i : ℕ) : Prop :=
  0 < digitAt p N i
end PascalMinusOne


