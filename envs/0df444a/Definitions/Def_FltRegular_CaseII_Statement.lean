-- Prove2me | Definitions.Def_FltRegular_CaseII_Statement
-- name    : FltRegular_CaseII_Statement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:13:13.776434+00:00
-- url     : https://prove2.me/theorems/6e536cab-640c-4ba2-ac24-9273adcf02f1
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseII/Statement.lean

module
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseII_InductionStep
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
set_option autoImplicit false
@[expose] public section
@[expose] public section
open scoped nonZeroDivisors NumberField
open Polynomial
variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
  (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
namespace FltRegular
end FltRegular


