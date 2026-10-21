-- Prove2me | Definitions.Def_MazurTransfer_OriginalRationalClosurePrimeValuationData20261019
-- name    : MazurTransfer_OriginalRationalClosurePrimeValuationData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T00:36:30.2927+00:00
-- url     : https://prove2.me/theorems/76737718-e13e-4d46-90d0-5a8f95827d3d
-- title:
--   Original embedded rational prime and integer-ring equivalence
-- statement:
--   Retain the original rational field inside the fixed closure, its rational equivalence, integer-ring equivalence, intrinsic prime certificate, height-one prime and rational unit map. All six complete original types, five whole constructor values, both original scoped provider types and four generated structural proof types are independently checked. Valuation normalization is a separate theorem interface. Named downstream consumer: the actual pi Selmer rational radicand prime-divisibility and thirteen-support theorem.
-- source:
--   MazurTheorem RationalClosurePrimeValuation by Vas and contributors; original constructor interface with complete original type and whole-value audits, preserving per-file Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: normalize the prime valuations on the ring of integers
of the embedded rational field in the fixed closure. Explicitly identify
its integer ring with Z and compare the normalized prime valuation with
the ordinary rational p-adic valuation.
The intrinsic primality certificate constructs the same height-one prime. Valuation normalization is proved separately.
Named downstream consumer: transport the actual pi Selmer inertia-derived
prime valuations to its rational radicand power-class coordinates.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.RationalClosurePrimeValuation
open NumberField IsDedekindDomain
local notation "F" => AlgebraicClosure ℚ
abbrev RationalField := (⊥ : IntermediateField ℚ F)
local instance instNumberFieldSubtypeAlgebraicClosureRatMemIntermediateFieldRationalField : NumberField RationalField := NumberField.of_module_finite ℚ RationalField

def rationalEquiv : RationalField ≃ₐ[ℚ] ℚ := IntermediateField.botEquiv ℚ F

def integerEquiv : 𝓞 RationalField ≃+* ℤ :=
  (RingOfIntegers.mapRingEquiv rationalEquiv.toRingEquiv).trans Rat.ringOfIntegersEquiv

local instance instIsPrincipalIdealRingRingOfIntegersSubtypeAlgebraicClosureRatMemIntermediateFieldRationalField : IsPrincipalIdealRing (𝓞 RationalField) :=
  IsPrincipalIdealRing.of_surjective integerEquiv.symm.toRingHom integerEquiv.symm.surjective

theorem prime_natCast (q : ℕ) (hq : q.Prime) : Prime (q : 𝓞 RationalField) := by
  apply (MulEquiv.prime_iff integerEquiv).mp
  rw [map_natCast]
  exact Nat.prime_iff_prime_int.mp hq

def rationalPrime (q : ℕ) [hq : Fact q.Prime] : HeightOneSpectrum (𝓞 RationalField) where
  asIdeal := Ideal.span {(q : 𝓞 RationalField)}
  isPrime := (Ideal.span_singleton_prime (Nat.cast_ne_zero.mpr hq.out.ne_zero)).mpr
    (prime_natCast q hq.out)
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hq.out.ne_zero







def rationalUnits (a : ℚˣ) : RationalFieldˣ :=
  Units.map (algebraMap ℚ RationalField : ℚ →* RationalField) a



end MazurTransfer.RationalClosurePrimeValuation
#print axioms MazurTransfer.RationalClosurePrimeValuation.RationalField
#print axioms MazurTransfer.RationalClosurePrimeValuation.rationalEquiv
#print axioms MazurTransfer.RationalClosurePrimeValuation.integerEquiv
#print axioms MazurTransfer.RationalClosurePrimeValuation.prime_natCast
#print axioms MazurTransfer.RationalClosurePrimeValuation.rationalPrime
#print axioms MazurTransfer.RationalClosurePrimeValuation.rationalUnits
#print axioms MazurTransfer.RationalClosurePrimeValuation.instNumberFieldSubtypeAlgebraicClosureRatMemIntermediateFieldRationalField
#print axioms MazurTransfer.RationalClosurePrimeValuation.instIsPrincipalIdealRingRingOfIntegersSubtypeAlgebraicClosureRatMemIntermediateFieldRationalField


