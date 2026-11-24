-- Prove2me | Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
-- name    : FltRegular_NumberTheory_SystemOfUnits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:32:46.330731+00:00
-- url     : https://prove2.me/theorems/7c65faf8-d10f-45da-ac8f-1d468f3357c4
-- title:
--   System Of Units
-- statement:
--   Definitions and structural lemmas for System Of Units, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/SystemOfUnits.lean

module
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
set_option autoImplicit false
@[expose] public section
@[expose] public section
open FiniteDimensional
open NumberField
variable (p : ℕ) (hp : Nat.Prime p)
open Module Finset
variable (G : Type*) [AddCommGroup G] (s : ℕ) (hf : finrank ℤ G = s * (p - 1))
local notation "A" => (CyclotomicIntegers p)
section
variable [Module (CyclotomicIntegers p) G]
structure systemOfUnits (s : ℕ) where
  /-- The family of units in the system. -/
  units : Fin s → G
  /-- The linear independence of the family over cyclotomic integers. -/
  linearIndependent : LinearIndependent A units
namespace systemOfUnits
include hp
include hf
end systemOfUnits
end
namespace systemOfUnits
include hp hf
variable [Module.Free ℤ G]
end systemOfUnits


