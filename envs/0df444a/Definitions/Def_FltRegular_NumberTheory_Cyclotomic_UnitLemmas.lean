-- Prove2me | Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
-- name    : FltRegular_NumberTheory_Cyclotomic_UnitLemmas
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:32:21.250355+00:00
-- url     : https://prove2.me/theorems/a42925b7-a048-4404-8f78-01f8e28b9bed
-- title:
--   Unit Lemmas
-- statement:
--   Definitions and structural lemmas for Unit Lemmas, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/UnitLemmas.lean

module
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
set_option autoImplicit false
@[expose] public section
@[expose] public section
variable {p : ℕ} [NeZero p] {K : Type*} [Field K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open scoped nonZeroDivisors NumberField
open IsCyclotomicExtension NumberField Polynomial IsCMField
noncomputable section
local notation3 "η" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
set_option quotPrecheck false
local notation "I" => (Ideal.span ({(η - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))
variable [NumberField K] [IsCyclotomicExtension {p} ℚ K]


