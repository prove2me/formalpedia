-- Prove2me | Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
-- name    : FltRegular_NumberTheory_CyclotomicRing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:32:18.528181+00:00
-- url     : https://prove2.me/theorems/29680899-b680-4744-b0a2-3afeda300aa9
-- title:
--   Cyclotomic Ring
-- statement:
--   Definitions and structural lemmas for Cyclotomic Ring, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/CyclotomicRing.lean

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_Rat
set_option autoImplicit false
@[expose] public section
@[expose] public section
noncomputable section
open Polynomial NumberField
variable (p : ℕ) [hpri : Fact p.Prime]
def CyclotomicIntegers : Type := AdjoinRoot (cyclotomic p ℤ)
instance : CommRing (CyclotomicIntegers p) := by
  delta CyclotomicIntegers
  infer_instance
open Polynomial in
lemma IsPrimitiveRoot.cyclotomic_eq_minpoly
    (x : 𝓞 (CyclotomicField p ℚ)) (hx : IsPrimitiveRoot x.1 p) :
    minpoly ℤ x = cyclotomic p ℤ := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (RingHom.injective_int (algebraMap ℤ ℚ))
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ (CyclotomicField p ℚ)
    (IsIntegralClosure.isIntegral _ (CyclotomicField p ℚ) _),
    ← cyclotomic_eq_minpoly_rat (n := p) (hpos := hpri.out.pos), map_cyclotomic]
  exact hx
namespace CyclotomicIntegers
@[simps! -isSimp]
def equiv :
    CyclotomicIntegers p ≃+* 𝓞 (CyclotomicField p ℚ) := by
  have H := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  have hH : minpoly ℤ H.integralPowerBasis.gen = cyclotomic p ℤ :=
    H.integralPowerBasis_gen ▸ IsPrimitiveRoot.cyclotomic_eq_minpoly p H.toInteger H
  exact (AdjoinRoot.equiv' (cyclotomic p ℤ) H.integralPowerBasis
    (hH ▸ ((AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self))
    (hH ▸ minpoly.aeval _ _)).toRingEquiv
instance : IsDomain (CyclotomicIntegers p) :=
  AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (cyclotomic.irreducible hpri.out.pos))
def zeta : CyclotomicIntegers p := AdjoinRoot.root _
def powerBasis : PowerBasis ℤ (CyclotomicIntegers p) :=
  AdjoinRoot.powerBasis' (cyclotomic.monic _ _)
instance : Module.Free ℤ (CyclotomicIntegers p) := ⟨_, (powerBasis p).basis⟩
lemma nontrivial {p} (hp : p ≠ 0) : Nontrivial (CyclotomicIntegers p) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  simp only [ne_eq, Ideal.span_singleton_eq_top]
  intro h
  have hdegree := natDegree_eq_zero_of_isUnit h
  rw [natDegree_cyclotomic] at hdegree
  exact hdegree.not_gt (Nat.totient_pos.2 <| Nat.zero_lt_of_ne_zero hp)
lemma charZero {p} (hp : p ≠ 0) : CharZero (CyclotomicIntegers p) :=
  have := nontrivial hp
  ⟨(FaithfulSMul.algebraMap_injective _ _).comp (algebraMap ℕ ℤ).injective_nat⟩
instance : CharZero (CyclotomicIntegers p) := charZero hpri.out.ne_zero
end CyclotomicIntegers
end


