-- Prove2me | Definitions.Def_FltRegular_SmallNumbers_Five_FLT5
-- name    : FltRegular_SmallNumbers_Five_FLT5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:14:25.160103+00:00
-- url     : https://prove2.me/theorems/d460d351-1636-4a77-8497-cf77693bf73d
-- title:
--   FLT5
-- statement:
--   Definitions and structural lemmas for FLT5, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Five/FLT5.lean

module
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Definitions.Def_FltRegular_FltRegular
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Nat NumberField IsCyclotomicExtension


