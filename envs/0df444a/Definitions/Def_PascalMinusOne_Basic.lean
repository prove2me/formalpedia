-- Prove2me | Definitions.Def_PascalMinusOne_Basic
-- name    : PascalMinusOne_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:16:43.6038+00:00
-- url     : https://prove2.me/theorems/13045076-2c38-4f07-ad9b-306f900f9147
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Upstream contributors (jfairfaxball-348/pascal-minus-one; see pinned Apache-2.0 LICENSE and README.md)'s pinned Pascal Minus-One GCD development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Basic.lean

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
set_option autoImplicit true
namespace PascalMinusOne
def admissibleIndices (N m : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun k ↦ 0 < k ∧ m ∣ k
def G (N m : ℕ) : ℕ :=
  (admissibleIndices N m).gcd fun k ↦ N.choose k
def Admissible (N m k : ℕ) : Prop :=
  0 < k ∧ k < N ∧ m ∣ k
end PascalMinusOne


