-- Prove2me | Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
-- name    : TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:47:26.658652+00:00
-- url     : https://prove2.me/theorems/3b21deb8-5b23-4537-9793-259157d1459a
-- title:
--   Counting carriers for ideals and prime ideals
-- statement:
--   For a number field $K$, prime ideals, nonzero integral ideals, and ideal prime powers are counted with the inclusive bound $\mathrm N I\leq x$. Weighted counts sum a given weight over the same sets; in particular,
--
--   $$
--   \pi_S(x)=\#\{P\in S:\mathrm N P\leq x\}.
--   $$
--
--   A prime-power ideal has its unique prime base and positive exponent. The underlying general bounded-norm construction uses rings free and finite over $\mathbb Z$; rings of integers satisfy these conditions.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Counting.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Counting.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
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
# Counting carriers for ideals and prime ideals

Every estimate in the arithmetic-Dirichlet-series roadmap counts objects whose absolute norm does
not exceed a *real* cutoff `x`, and always inclusively: an object of norm exactly `x` is counted.
This file fixes that convention once.

The common core is Mathlib's `Northcott` property: a function `N : ι → ℕ` is Northcott when each
set `{i | N i ≤ B}` is finite.  For such an `N`:

* `TauCeti.normLE N x` is the finite set of indices with `(N i : ℝ) ≤ x`;
* `TauCeti.summatory N w x` is the inclusive sum of a weight `w` over `TauCeti.normLE N x`.

Two instances of this core carry the arithmetic content, `TauCeti.idealsLE` for the nonzero
integral ideals of `𝓞 K` and `TauCeti.primesLE` for the height-one primes, with
`TauCeti.idealSummatory`, `TauCeti.primeSummatory`, and `TauCeti.primePowerSummatory` the associated
summatory functions.  The
weighted prime counts of the roadmap are the two named specializations
`TauCeti.primeTheta`, the logarithmically weighted count, and `TauCeti.primeCount`, the
unweighted one; both are restricted to a set `S` of height-one primes through `Set.indicator`,
so no decidability hypothesis is needed on `S`.

A prime-power ideal is `𝔭 ^ k` for a unique height-one prime `𝔭` and a unique `k ≥ 1`;
`TauCeti.primePowerBase` and `TauCeti.primePowerExponent` name that pair, and
`TauCeti.idealPrimePower_eq_of_base_eq_of_exponent_eq` records that it determines the ideal.  The
exponent is `1` exactly on the primes themselves, which is `TauCeti.primePowerExponent_eq_one_iff`;
`TauCeti.IdealPrimePower.ofPrime` is the resulting inclusion of the prime carrier into the
prime-power carrier, and `TauCeti.primePowerSummatory_eq_primeSummatory` uses it to read a
prime-power sum concentrated on the exponent-one part as a sum over primes.

`TauCeti.idealsLE_filter_dvd` identifies the ideals below a cutoff divisible by a fixed nonzero
ideal `P` with the multiples of `P`, and `TauCeti.idealSummatory_ite_dvd` reads the corresponding
part of a summatory function at the rescaled cutoff `x / N(P)`.

Two lemmas move a summatory function between the three carriers.
`TauCeti.idealSummatory_eq_primePowerSummatory` reads an ideal weight vanishing off the prime
powers as a prime-power weight, and `TauCeti.idealSummatory_eq_sum_range_normFiber` regroups an
ideal summatory function into the partial sum, over `n ≤ ⌊x⌋₊`, of the total mass on the norm
fibre at `n`; `TauCeti.idealSummatory_eq_sum_Icc_normCoeff` writes the same regrouping as a
partial sum of `TauCeti.normCoeff`.  Together they present a sum over prime powers as a partial
sum of an `ArithmeticFunction`, which is the shape a Tauberian theorem consumes.

For `0 ≤ x`, a real cutoff and its floor select the same indices, so
`TauCeti.normLE_eq_normLE_natFloor` and `TauCeti.summatory_eq_summatory_natFloor` convert between
the real and natural conventions. The small-cutoff cases are degenerate for a reason worth
recording: a nonzero ideal has absolute norm at least `1`, and a height-one prime at least `2`, so
`TauCeti.idealsLE_one` isolates the unit ideal and `TauCeti.primesLE_eq_empty_of_lt_two` empties the
prime carrier below `2`.

Modifying a weight on a finite set, or a prime set on a finite symmetric difference, changes a
summatory function by a quantity that is eventually the *constant* total discrepancy; this is
`TauCeti.eventually_summatory_sub_eq` and its two prime specializations. Layer 7 uses these to
show that finite changes do not affect a density. In the same spirit,
`TauCeti.primeTheta_isLittleO_of_finite` records that a finite set of primes contributes an
eventually constant amount to `ϑ_K`, hence `o(x)`: an exceptional set can be discarded from a
counting argument outright, not merely from a density. Its `ψ` companion is
`TauCeti.primePsi_isLittleO_of_finite`.

## Roadmap role

This is Layer **4** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: the finite cutoff
carriers of 4.1, the generic summatory functions on ideals, primes, and prime powers of 4.2, and the
weighted prime counts `primeTheta` and `primeCount` of 4.3. Layer 5 supplies the actual size
estimates for these counts, and consumes the prime base and exponent of a prime-power ideal to
fibre those estimates over the primes.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters I--II.
* H. Davenport, *Multiplicative Number Theory*, Chapters 1 and 7.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

namespace TauCeti

open Filter
open scoped nonZeroDivisors NumberField
open IsDedekindDomain

/-! ### Ideals and height-one primes of bounded absolute norm -/

/-- The absolute norm on nonzero ideals of an infinite Dedekind domain with finite quotients is
Northcott, by `Ring.HasFiniteQuotients.finite_absNorm_le`. Mathlib already supplies the
corresponding instance on height-one primes. -/
instance instNorthcottAbsNormNonZeroDivisors {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Infinite R] [Ring.HasFiniteQuotients R] [Module.Free ℤ R] [Module.Finite ℤ R] :
    Northcott (fun I : (Ideal R)⁰ ↦ Ideal.absNorm (I : Ideal R)) := by
  constructor
  intro B
  exact (Ring.HasFiniteQuotients.finite_absNorm_le (R := R) B).preimage
    Subtype.val_injective.injOn

variable (K : Type*) [Field K] [NumberField K]

/-- The nonzero integral ideals of `𝓞 K` of absolute norm at most `x`. -/
noncomputable abbrev idealsLE (x : ℝ) : Finset ((Ideal (𝓞 K))⁰) :=
  normLE (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) x

/-- The height-one primes of `𝓞 K` of absolute norm at most `x`. -/
noncomputable abbrev primesLE (x : ℝ) : Finset (HeightOneSpectrum (𝓞 K)) :=
  normLE (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal) x

/-- A nonzero integral ideal which is a positive power of a prime ideal. -/
abbrev IdealPrimePower :=
  {A : (Ideal (𝓞 K))⁰ // IsPrimePow (A : Ideal (𝓞 K))}

/-- Absolute norm is Northcott on prime-power ideals, by restriction from nonzero ideals. -/
instance instNorthcottAbsNormIdealPrimePower :
    Northcott (fun A : IdealPrimePower K ↦ Ideal.absNorm (A : Ideal (𝓞 K))) :=
  ⟨fun B ↦ (Northcott.finite_le
    (h := fun A : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (A : Ideal (𝓞 K))) B).preimage
      fun _ _ _ _ h ↦ Subtype.ext h⟩

/-- The prime-power ideals of `𝓞 K` of absolute norm at most `x`. -/
noncomputable abbrev primePowersLE (x : ℝ) : Finset (IdealPrimePower K) :=
  normLE (fun A : IdealPrimePower K ↦ Ideal.absNorm (A : Ideal (𝓞 K))) x



variable {K}



/-- The absolute norm of a height-one prime is at least `2`, as a real number. -/
theorem two_le_absNorm_asIdeal_real (v : HeightOneSpectrum (𝓞 K)) :
    (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v



/-! ### The prime base and the exponent of a prime-power ideal -/

/-- The **exponent** of a prime-power ideal `A`: the unique `k ≥ 1` with `A = 𝔭 ^ k`. -/
noncomputable def primePowerExponent (A : IdealPrimePower K) : ℕ :=
  A.2.choose_spec.choose

/-- The **prime base** of a prime-power ideal `A`: the unique height-one prime `𝔭` with
`A = 𝔭 ^ k` for some `k ≥ 1`. -/
noncomputable def primePowerBase (A : IdealPrimePower K) : HeightOneSpectrum (𝓞 K) where
  asIdeal := A.2.choose
  isPrime := Ideal.isPrime_of_prime A.2.choose_spec.choose_spec.1
  ne_bot := A.2.choose_spec.choose_spec.1.ne_zero

/-- The ideal underlying the prime base of a prime-power ideal is prime. -/
theorem prime_primePowerBase (A : IdealPrimePower K) : Prime (primePowerBase A).asIdeal :=
  A.2.choose_spec.choose_spec.1

omit [NumberField K] in
/-- The exponent of a prime-power ideal is positive. -/
theorem primePowerExponent_pos (A : IdealPrimePower K) : 0 < primePowerExponent A :=
  A.2.choose_spec.choose_spec.2.1

/-- The defining factorization of a prime-power ideal. -/
theorem primePowerBase_pow_primePowerExponent (A : IdealPrimePower K) :
    (primePowerBase A).asIdeal ^ primePowerExponent A = (A : Ideal (𝓞 K)) :=
  A.2.choose_spec.choose_spec.2.2

/-- The prime base is determined by any factorization of `A` as a power of a prime. -/
theorem primePowerBase_asIdeal_eq {A : IdealPrimePower K} {P : Ideal (𝓞 K)} (hP : Prime P)
    {k : ℕ} (hpow : P ^ k = (A : Ideal (𝓞 K))) :
    (primePowerBase A).asIdeal = P :=
  eq_of_prime_pow_eq (prime_primePowerBase A) hP (primePowerExponent_pos A)
    ((primePowerBase_pow_primePowerExponent A).trans hpow.symm)









/-- The exponent is determined by any factorization of `A` as a power of a prime. -/
theorem primePowerExponent_eq {A : IdealPrimePower K} {P : Ideal (𝓞 K)} (hP : Prime P)
    {k : ℕ} (hpow : P ^ k = (A : Ideal (𝓞 K))) :
    primePowerExponent A = k := by
  have hbase : (primePowerBase A).asIdeal = P := primePowerBase_asIdeal_eq hP hpow
  have hnorm : Ideal.absNorm P ^ primePowerExponent A = Ideal.absNorm P ^ k := by
    rw [← map_pow, ← map_pow, hpow, ← hbase, primePowerBase_pow_primePowerExponent A]
  refine Nat.pow_right_injective ?_ hnorm
  have h2 : (2 : ℝ) ≤ Ideal.absNorm (primePowerBase A).asIdeal :=
    two_le_absNorm_asIdeal_real _
  rw [hbase] at h2
  exact_mod_cast h2







/-- A height-one prime, seen as the prime-power ideal of exponent one that it is. -/
def IdealPrimePower.ofPrime (v : HeightOneSpectrum (𝓞 K)) : IdealPrimePower K :=
  ⟨⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩,
    v.asIdeal, 1, Ideal.prime_of_isPrime v.ne_bot v.isPrime, one_pos, pow_one _⟩





























variable (K)

/-! ### Summatory functions over ideals and over primes -/



/-- The inclusive summatory function of a weight on the nonzero integral ideals of `𝓞 K`. -/
noncomputable abbrev idealSummatory {M : Type*} [AddCommMonoid M]
    (w : (Ideal (𝓞 K))⁰ → M) (x : ℝ) : M :=
  summatory (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) w x

/-- The inclusive summatory function of a weight on the height-one primes of `𝓞 K`. -/
noncomputable abbrev primeSummatory {M : Type*} [AddCommMonoid M]
    (w : HeightOneSpectrum (𝓞 K) → M) (x : ℝ) : M :=
  summatory (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal) w x

/-- The inclusive summatory function of a weight on prime-power ideals of `𝓞 K`. -/
noncomputable abbrev primePowerSummatory {M : Type*} [AddCommMonoid M]
    (w : IdealPrimePower K → M) (x : ℝ) : M :=
  summatory (fun A : IdealPrimePower K ↦ Ideal.absNorm (A : Ideal (𝓞 K))) w x

























variable {K}

namespace MultiplicativeIdealWeight

variable (χ : MultiplicativeIdealWeight K)



end MultiplicativeIdealWeight

variable (K)









/-! ### The weighted prime counts -/

/-- The logarithmically weighted count of the primes of `S` of absolute norm at most `x`: the
number-field analogue of Chebyshev's `ϑ`. -/
noncomputable def primeTheta (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : ℝ :=
  primeSummatory K (S.indicator fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) x

/-- The number of primes of `S` of absolute norm at most `x`, as a real number: the number-field
analogue of `π`. -/
noncomputable def primeCount (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : ℝ :=
  primeSummatory K (S.indicator 1) x

variable {K}
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {x : ℝ}

























































end TauCeti

end
end


