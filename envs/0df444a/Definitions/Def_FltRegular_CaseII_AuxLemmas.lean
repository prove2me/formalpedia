-- Prove2me | Definitions.Def_FltRegular_CaseII_AuxLemmas
-- name    : FltRegular_CaseII_AuxLemmas
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:31:46.784851+00:00
-- url     : https://prove2.me/theorems/f377d8bf-6a96-42e0-93de-6acd0aaf2364
-- title:
--   Aux Lemmas
-- statement:
--   Definitions and structural lemmas for Aux Lemmas, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseII/AuxLemmas.lean

module
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
set_option autoImplicit false
@[expose] public section
@[expose] public section
variable {K : Type*} {p : ℕ} [Field K] [CharZero K] {ζ : K}
open scoped nonZeroDivisors
open Polynomial


