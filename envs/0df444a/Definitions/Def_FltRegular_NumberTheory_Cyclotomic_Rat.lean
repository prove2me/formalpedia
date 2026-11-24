-- Prove2me | Definitions.Def_FltRegular_NumberTheory_Cyclotomic_Rat
-- name    : FltRegular_NumberTheory_Cyclotomic_Rat
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:31:47.835903+00:00
-- url     : https://prove2.me/theorems/5aaa8be6-5e3f-41a0-873d-5ae257c05fae
-- title:
--   Rat
-- statement:
--   Definitions and structural lemmas for Rat, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/Rat.lean

module
public import Mathlib.NumberTheory.Cyclotomic.Basic
set_option autoImplicit false
@[expose] public section
public section
@[expose] section
instance instIsCyclotomicExtensionSingletonNatSetRatCyclotomicField_fltRegular (n : ℕ) : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero n ℚ
end


