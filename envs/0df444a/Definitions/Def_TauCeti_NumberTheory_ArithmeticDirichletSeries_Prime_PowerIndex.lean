-- Prove2me | Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_PowerIndex
-- name    : TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_PowerIndex
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:53:36.53841+00:00
-- url     : https://prove2.me/theorems/39649210-f9e7-40cd-811e-e8460422970d
-- title:
--   Indexing the prime-power ideals by a prime and an exponent
-- statement:
--   For a number field $K$, prime ideals with a natural-number index parametrize all nonzero prime-power ideals:
--
--   $$
--   (P,k)\longmapsto P^{k+1}.
--   $$
--
--   The map is a bijection. It gives an index set for prime-power Dirichlet series.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/PowerIndex.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/PowerIndex.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Indexing the prime-power ideals by a prime and an exponent

Every prime-power ideal of `𝓞 K` is `𝔭 ^ (k + 1)` for a unique height-one prime `𝔭` and a unique
`k : ℕ`. This file records that bijection and what it does to an infinite sum: a *summable* family
on the prime-power ideals has the same sum as the iterated sum over primes and exponents, and a
*summable* family on *all* nonzero ideals collapses to that same iterated sum whenever it is
supported on prime powers. Both statements assume summability; neither asserts it.

This is the ideal analogue of Mathlib's `Nat.Primes.prodNatEquiv` and the two summation lemmas
built on it, `tsum_primes_pow_eq` and `tsum_eq_tsum_primes_of_support_subset_prime_powers`. Those
are what turns an Euler-product logarithm, which is naturally indexed by `(𝔭, k)`, into a Dirichlet
series indexed by ideals — the shape a von Mangoldt coefficient identity needs.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.idealPrimePowerOf`: the prime-power ideal `𝔭 ^ (k + 1)`.
* `TauCeti.idealPrimePowerEquiv`: the bijection `(𝔭, k) ↦ 𝔭 ^ (k + 1)` onto the prime-power ideals.

## Main results

* `TauCeti.summable_comp_idealPrimePowerOf`: a summable family on all nonzero ideals remains
  summable after restriction to the positive prime powers.
* `TauCeti.summable_tsum_norm_idealPrimePowerOf`: the prime-power tails of an absolutely
  summable ideal-indexed family are summable over the primes.
* `TauCeti.tsum_idealPrimePower_eq`: a summable family on the prime-power ideals has the same sum
  as the iterated sum over primes and exponents.
* `TauCeti.tsum_eq_tsum_idealPrimePower_of_support_subset`: a summable family on the nonzero
  ideals supported on prime powers has the same sum as that iterated sum.

## Implementation notes

The inverse sends `A` to `(primePowerBase A, primePowerExponent A - 1)`. The truncated subtraction
is harmless because `primePowerExponent A` is positive, and the `+ 1` in the forward map is what
keeps the exponent positive without carrying a hypothesis.
-/

 section

open scoped nonZeroDivisors NumberField
open IsDedekindDomain NumberField TauCeti

variable {K : Type*} [Field K] [NumberField K]

namespace IsDedekindDomain.HeightOneSpectrum

/-- The prime-power ideal `𝔭 ^ (k + 1)`. -/
def idealPrimePowerOf (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) : IdealPrimePower K :=
  ⟨⟨P.asIdeal ^ (k + 1), pow_mem (mem_nonZeroDivisors_of_ne_zero P.ne_bot) _⟩,
    ⟨P.asIdeal, k + 1, Ideal.prime_of_isPrime P.ne_bot P.isPrime, k.succ_pos, rfl⟩⟩

@[simp]
theorem coe_idealPrimePowerOf (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    ((P.idealPrimePowerOf k : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = P.asIdeal ^ (k + 1) :=
  (rfl)



@[simp]
theorem primePowerBase_idealPrimePowerOf (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    primePowerBase (P.idealPrimePowerOf k) = P :=
  HeightOneSpectrum.ext
    (primePowerBase_asIdeal_eq (Ideal.prime_of_isPrime P.ne_bot P.isPrime)
      (P.coe_idealPrimePowerOf k).symm)

@[simp]
theorem primePowerExponent_idealPrimePowerOf (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    primePowerExponent (P.idealPrimePowerOf k) = k + 1 :=
  primePowerExponent_eq (Ideal.prime_of_isPrime P.ne_bot P.isPrime)
    (P.coe_idealPrimePowerOf k).symm

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

/-- **A prime-power ideal is a prime and an exponent.** The bijection `(𝔭, k) ↦ 𝔭 ^ (k + 1)` from
height-one primes and natural numbers onto the prime-power ideals of `𝓞 K`.

This is the ideal analogue of `Nat.Primes.prodNatEquiv`. -/
noncomputable def idealPrimePowerEquiv :
    HeightOneSpectrum (𝓞 K) × ℕ ≃ IdealPrimePower K where
  toFun Pk := Pk.1.idealPrimePowerOf Pk.2
  invFun A := (primePowerBase A, primePowerExponent A - 1)
  left_inv := by
    rintro ⟨P, k⟩
    simp
  right_inv A := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [HeightOneSpectrum.coe_idealPrimePowerOf, Nat.sub_add_cancel (primePowerExponent_pos A)]
    exact primePowerBase_pow_primePowerExponent A

end TauCeti

namespace IsDedekindDomain.HeightOneSpectrum



end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti



variable {α : Type*} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α] [CompleteSpace α]
  {f : (Ideal (𝓞 K))⁰ → α}



section Norm

variable {β : Type*} [NormedAddCommGroup β] {g : (Ideal (𝓞 K))⁰ → β}



end Norm

variable [T0Space α]





end TauCeti

end
end


