-- Prove2me | Definitions.Def_FltRegular_SmallNumbers_Seven_Seven
-- name    : FltRegular_SmallNumbers_Seven_Seven
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:31:50.704062+00:00
-- url     : https://prove2.me/theorems/d8a3d73b-a1ee-4ff9-b675-b851a82af77d
-- title:
--   Seven
-- statement:
--   Definitions and structural lemmas for Seven, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Seven/Seven.lean

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.Tactic.NormNum.Prime
set_option autoImplicit false
@[expose] public section
@[expose] public section
open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers
  IsCyclotomicExtension.Rat Polynomial cyclotomic Ideal
variable {K : Type*} [Field K] [NumberField K]
local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)
instance Nat.fact_prime_seven : Fact (Nat.Prime 7) :=
  ⟨prime_seven⟩
variable [IsCyclotomicExtension {7} ℚ K]


