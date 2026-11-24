-- Prove2me | Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
-- name    : FltRegular_NumberTheory_Cyclotomic_CaseI
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:32:47.74048+00:00
-- url     : https://prove2.me/theorems/748a2200-72f0-49d9-b04f-94dd801d464b
-- title:
--   Case I
-- statement:
--   Definitions and structural lemmas for Case I, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CaseI.lean

module
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
set_option autoImplicit false
@[expose] public section
@[expose] public section
open scoped NumberField nonZeroDivisors
variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
local notation3 "zetaUnit" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
open FractionalIdeal NumberField IsCMField
namespace FltRegular.CaseI
end FltRegular.CaseI


