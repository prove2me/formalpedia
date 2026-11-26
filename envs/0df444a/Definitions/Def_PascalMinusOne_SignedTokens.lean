-- Prove2me | Definitions.Def_PascalMinusOne_SignedTokens
-- name    : PascalMinusOne_SignedTokens
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:16:45.864041+00:00
-- url     : https://prove2.me/theorems/9e87e6c9-a85d-5f2a-85a8-62b627fce231
-- title:
--   Signed Tokens
-- statement:
--   Definitions and structural lemmas for Signed Tokens, from Upstream contributors (jfairfaxball-348/pascal-minus-one; see pinned Apache-2.0 LICENSE and README.md)'s pinned Pascal Minus-One GCD development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SignedTokens.lean

import Mathlib.Data.Int.Basic
import Mathlib.Tactic
set_option autoImplicit true
namespace PascalMinusOne
def SignedZeroSum (m A B : ℕ) : Prop :=
  (m : ℤ) ∣ (A : ℤ) - (B : ℤ)
def HasProperZeroSubmultiset (m A B : ℕ) : Prop :=
  ∃ a b : ℕ,
    a ≤ A ∧ b ≤ B ∧
    0 < a + b ∧ a + b < A + B ∧
    SignedZeroSum m a b
def MinimalSignedZeroSum (m A B : ℕ) : Prop :=
  0 < A + B ∧ SignedZeroSum m A B ∧ ¬ HasProperZeroSubmultiset m A B
end PascalMinusOne


