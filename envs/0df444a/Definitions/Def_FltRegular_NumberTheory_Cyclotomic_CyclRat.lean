-- Prove2me | Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat
-- name    : FltRegular_NumberTheory_Cyclotomic_CyclRat
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:31:46.480017+00:00
-- url     : https://prove2.me/theorems/a32e8298-9888-47e9-b276-dae6a174158c
-- title:
--   Cycl Rat
-- statement:
--   Definitions and structural lemmas for Cycl Rat, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CyclRat.lean

module
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
set_option autoImplicit false
@[expose] public section
@[expose] public section
open FiniteDimensional Polynomial Algebra Nat Finset Fintype
variable (p : ℕ) (L : Type*) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
section IntFacts
open scoped NumberField
open Ideal IsCyclotomicExtension
local notation "R" => 𝓞 (CyclotomicField p ℚ)
@[nolint unusedArguments]
noncomputable def fltIdeals [Fact p.Prime] (x y : ℤ) {η : R} (_ : η ∈ nthRootsFinset p 1) : Ideal R :=
  Ideal.span ({x + η * y} : Set R)
variable {p}
open IsPrimitiveRoot
variable {L}
end IntFacts


