-- Prove2me | Definitions.Def_FltRegular_NumberTheory_KummersLemma_KummersLemma
-- name    : FltRegular_NumberTheory_KummersLemma_KummersLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:11:35.008591+00:00
-- url     : https://prove2.me/theorems/f91fa4c4-b143-4496-80a1-9ddbd965dd9a
-- title:
--   Kummers Lemma
-- statement:
--   Definitions and structural lemmas for Kummers Lemma, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/KummersLemma/KummersLemma.lean

module
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Hilbert94
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_Field
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Polynomial IsCyclotomicExtension.Rat
open scoped NumberField
variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
  (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
  {ζ : K} (hζ : IsPrimitiveRoot ζ p)
include hp hreg


