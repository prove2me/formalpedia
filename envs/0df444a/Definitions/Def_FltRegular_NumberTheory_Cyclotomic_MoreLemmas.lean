-- Prove2me | Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
-- name    : FltRegular_NumberTheory_Cyclotomic_MoreLemmas
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:31:44.849798+00:00
-- url     : https://prove2.me/theorems/a05983e4-7a30-40ce-bdc7-9390be2b9c2f
-- title:
--   More Lemmas
-- statement:
--   Definitions and structural lemmas for More Lemmas, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean

module
public import Mathlib.RingTheory.NormTrace
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
set_option autoImplicit false
@[expose] public section
@[expose] public section
variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open scoped nonZeroDivisors NumberField
open Polynomial IsCyclotomicExtension.Rat
variable (hp : p ≠ 2)


