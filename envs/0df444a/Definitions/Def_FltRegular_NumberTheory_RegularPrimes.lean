-- Prove2me | Definitions.Def_FltRegular_NumberTheory_RegularPrimes
-- name    : FltRegular_NumberTheory_RegularPrimes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:32:20.030679+00:00
-- url     : https://prove2.me/theorems/9357e3b3-35cc-454c-844a-c6cf6e779b3d
-- title:
--   Regular Primes
-- statement:
--   Definitions and structural lemmas for Regular Primes, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/RegularPrimes.lean

module
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_Rat
set_option autoImplicit false
@[expose] public section
@[expose] public section
noncomputable section
open Nat Polynomial NumberField
open scoped NumberField
variable (n p : ℕ)
def IsRegularNumber : Prop :=
  n.Coprime <| Fintype.card <| ClassGroup (𝓞 <| CyclotomicField n ℚ)
def IsRegularPrime : Prop :=
  IsRegularNumber p
section TwoRegular
variable (K : Type*) [Field K]
variable (L : Type*) [Field L] [Algebra K L]
def cyclotomicFieldTwoEquiv [IsCyclotomicExtension {2} K L] : L ≃ₐ[K] K := by
  suffices IsSplittingField K K (cyclotomic 2 K) by
    have : IsSplittingField K L (cyclotomic 2 K) :=
      IsCyclotomicExtension.splitting_field_cyclotomic 2 K L
    exact (IsSplittingField.algEquiv L (cyclotomic 2 K)).trans
      (IsSplittingField.algEquiv K <| cyclotomic 2 K).symm
  exact ⟨by simpa using Splits.X_sub_C (-1 : K),
    by simp [eq_iff_true_of_subsingleton]⟩
instance IsPrincipalIdealRing_of_IsCyclotomicExtension_two
    (L : Type*) [Field L] [CharZero L] [IsCyclotomicExtension {2} ℚ L] :
    IsPrincipalIdealRing (𝓞 L) :=
  let F : 𝓞 L ≃+* ℤ := (RingOfIntegers.mapRingEquiv
    (cyclotomicFieldTwoEquiv ℚ L).toRingEquiv).trans Rat.ringOfIntegersEquiv
  IsPrincipalIdealRing.of_surjective F.symm.toRingHom F.symm.surjective
end TwoRegular


