-- Prove2me | Definitions.Def_FltRegular_NumberTheory_Hilbert94
-- name    : FltRegular_NumberTheory_Hilbert94
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:11:04.460671+00:00
-- url     : https://prove2.me/theorems/eba9ad03-515f-4144-982a-37f6f20710d3
-- title:
--   Hilbert94
-- statement:
--   Definitions and structural lemmas for Hilbert94, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert94.lean

module
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Theorems.Thm_Hilbert92

set_option autoImplicit false
@[expose] public section
@[expose] public section
open scoped NumberField
variable {K : Type} [Field K]
open Polynomial Module
variable {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
    [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L]
variable [IsGalois K L]


