-- Prove2me | Definitions.Def_MillerRabin_Mathlib_Algebra_Ring_Int_Parity
-- name    : MillerRabin_Mathlib_Algebra_Ring_Int_Parity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:10:07.449796+00:00
-- url     : https://prove2.me/theorems/468dca80-8f03-464d-8633-4f769b575308
-- title:
--   Parity
-- statement:
--   Definitions and structural lemmas for Parity, from hanwenzhu/miller-rabin contributors (see pinned LICENSE and source headers)'s pinned Miller–Rabin primality test error bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Algebra/Ring/Int/Parity.lean

import Mathlib.Algebra.Ring.Int.Parity
set_option autoImplicit false
variable {α : Type*}
section GroupWithZero
variable [GroupWithZero α] [HasDistribNeg α] {n : ℤ}
end GroupWithZero
section Group
variable [Group α] [HasDistribNeg α] {n : ℤ}
end Group


