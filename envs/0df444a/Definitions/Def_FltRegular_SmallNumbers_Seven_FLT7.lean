-- Prove2me | Definitions.Def_FltRegular_SmallNumbers_Seven_FLT7
-- name    : FltRegular_SmallNumbers_Seven_FLT7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:14:28.072148+00:00
-- url     : https://prove2.me/theorems/a5fd509d-d818-45ea-8dee-1c5ecf3ee9ca
-- title:
--   FLT7
-- statement:
--   Definitions and structural lemmas for FLT7, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Seven/FLT7.lean

module
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_FltRegular_FltRegular
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_SmallNumbers_Seven_Seven
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Nat NumberField IsCyclotomicExtension


