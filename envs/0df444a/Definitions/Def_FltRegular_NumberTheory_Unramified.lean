-- Prove2me | Definitions.Def_FltRegular_NumberTheory_Unramified
-- name    : FltRegular_NumberTheory_Unramified
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:31:45.713356+00:00
-- url     : https://prove2.me/theorems/38fe4547-3f43-4588-acec-dfbfb09cc7ad
-- title:
--   Unramified
-- statement:
--   Definitions and structural lemmas for Unramified, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Unramified.lean

module
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Unramified.Locus
set_option autoImplicit false
@[expose] public section
@[expose] public section
open UniqueFactorizationMonoid Ideal
attribute [local instance] FractionRing.liftAlgebra
variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]
variable {R} {S}
open nonZeroDivisors Polynomial


