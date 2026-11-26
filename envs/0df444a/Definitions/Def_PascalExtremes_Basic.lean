-- Prove2me | Definitions.Def_PascalExtremes_Basic
-- name    : PascalExtremes_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:53:47.149549+00:00
-- url     : https://prove2.me/theorems/f8c325e2-bd5b-43a4-a04b-b1331e969c0f
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Upstream contributors (jfairfaxball-348/Pascal-Extremes; adapted in part under Apache-2.0 from jfairfaxball-348/pascal-minus-one; see pinned LICENSE and README.md)'s pinned Pascal Extremes: sharp prime-power divisibility and least extremal rows for restricted binomial gcds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/Basic.lean

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PascalExtremes
def admissibleIndices (N m : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun k ↦ 0 < k ∧ m ∣ k
def G (N m : ℕ) : ℕ :=
  (admissibleIndices N m).gcd fun k ↦ N.choose k
def AdmissibleRow (m N : ℕ) : Prop :=
  m < N ∧ m ∣ N
def Admissible (N m k : ℕ) : Prop :=
  0 < k ∧ k < N ∧ m ∣ k
end PascalExtremes


