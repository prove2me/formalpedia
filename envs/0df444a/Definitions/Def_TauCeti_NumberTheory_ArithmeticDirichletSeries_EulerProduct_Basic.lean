-- Prove2me | Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Basic
-- name    : TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Basic
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:43:27.678817+00:00
-- url     : https://prove2.me/theorems/b0705eff-7ce0-4c05-b6d1-0297ce646dc8
-- title:
--   Canonical local factors and formal Euler products for ideal arithmetic functions
-- statement:
--   For an ideal arithmetic function $f$ and a nonzero prime ideal $P$, the local coefficient sequence is $e\mapsto f(P^e)$. Restricting $f$ to ideals supported on a finite set of primes and forming these local sequences supplies the algebraic factors of an Euler product.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Basic.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Basic.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Canonical local factors and formal Euler products for ideal arithmetic functions

This file develops the Euler-product layer for arithmetic functions on nonzero ideals. It builds
the canonical formal power series at each height-one prime and sends that series into Mathlib's
`ArithmeticFunction.ofPowerSeries` API. The resulting local arithmetic factor has the prescribed
prime-power values and vanishes away from powers of the prime-ideal norm.

It then restricts an ideal arithmetic function to the nonzero ideals whose prime factors lie in a
prescribed set of height-one primes, and proves that for a *finite* set of primes the norm
coefficients of that restriction are exactly the product of the local factors, taken in Mathlib's
Dirichlet convolution of arithmetic functions. Passing to Mathlib's formal Euler product gives the
norm coefficients of the original function. Everything here is a formal identity of coefficients:
no analytic convergence hypothesis enters.

## Main definitions

* `TauCeti.IdealArithmeticFunction.localPowerSeries` has coefficient `f (P ^ n)` at `n`.
* `TauCeti.IdealArithmeticFunction.localArithmeticFactor` realizes that power series as an
  arithmetic function supported on powers of `N(P)`.
* `TauCeti.IdealArithmeticFunction.supportedPart f S` is `f` restricted to the nonzero ideals all
  of whose prime factors lie in `S`, and zero elsewhere.

## Main results

* `TauCeti.IdealArithmeticFunction.supportedPart_insert`: for a multiplicative `f`, adjoining one
  prime to the support convolves the restriction with the restriction to the powers of that prime.
* `TauCeti.IdealArithmeticFunction.normCoeff_supportedPart`: the **finite Euler product**
  `normCoeff (supportedPart f S) = ∏ P ∈ S, localArithmeticFactor f P` for a multiplicative `f`
  and a finite set `S` of height-one primes.
* `TauCeti.IdealArithmeticFunction.normCoeff_eq_eulerProduct`: the norm coefficients of a
  multiplicative ideal arithmetic function are Mathlib's formal Euler product of its canonical
  local factors.

## Implementation notes

"Supported on `S`" is spelled `Ideal.IsPrimeTo · Sᶜ`: no prime *outside* `S` divides the ideal.
That predicate, and the splitting `Ideal.IsPrimeTo.exists_eq_pow_mul` of an ideal into a prime
power times a cofactor together with its uniqueness `Ideal.eq_and_eq_of_pow_mul_eq_pow_mul`, live
in `TauCeti/RingTheory/DedekindDomain/Ideal.lean`, since nothing in them is specific to a number
field. Uniqueness is what makes the induction work: it is why exactly one summand of the ideal
convolution survives at each ideal. The multiplicativity of `f` over a prime-power factorization,
`TauCeti.IdealArithmeticFunction.IsMultiplicative.map_prod_pow`, likewise lives with the predicate
it elaborates, in `TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean`.

`TauCeti.MultiplicativeIdealWeight.restrict` is the opposite regime and is not a substitute:
it restricts *away from* a **finite** set of primes and stays inside the bundled weight carrier. A
finite Euler product needs support on a *finite* set of primes, so all but finitely many primes are
bad; such a function is never a `MultiplicativeIdealWeight`, whose zero support is finite by
definition. Hence `supportedPart` is a plain ideal arithmetic function.

Finiteness is what carries the finite products to the full Euler product. A nonzero ideal has
only finitely many prime divisors, and only finitely many primes have norm at most a given `n`, so
at a fixed norm coefficient the restriction `supportedPart f S` already agrees with `f` as soon as
`S` contains those primes. Each finite product is therefore eventually the exact norm coefficient,
and Mathlib's `ArithmeticFunction.eulerProduct`, being the limit of those finite products, computes
the norm coefficients of `f` itself. The local factors are derived from `f` rather than stored, so
this identity holds for any multiplicative `f` with no further data.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.eulerProduct` APIs.
* `TauCetiRoadmap/ArithmeticDirichletSeries/Suggested.lean`, whose local-factor target signatures
  and naming are adapted here.
-/

 section

open scoped nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K]

/-- The `e`-th power of a height-one prime of `𝓞 K`, as a nonzero integral ideal. -/
def primeIdealPow (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) : (Ideal (𝓞 K))⁰ :=
  ⟨P.asIdeal ^ e, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero e P.ne_bot)⟩



variable [NumberField K]







end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti



namespace IdealArithmeticFunction

variable {K : Type*} [Field K]

variable [NumberField K]

/-- The canonical local power series of `f` at a height-one prime `P`; its coefficient at `n` is
the value of `f` at the nonzero ideal `P ^ n`. -/
noncomputable def localPowerSeries (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    f ⟨P.asIdeal ^ n, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n P.ne_bot)⟩





/-- The canonical local arithmetic factor at `P`, obtained by substituting `N(P)⁻ˢ` into the
formal prime-power series through Mathlib's `ArithmeticFunction.ofPowerSeries`. -/
noncomputable def localArithmeticFactor (f : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) : ArithmeticFunction ℂ :=
  ArithmeticFunction.ofPowerSeries (Ideal.absNorm P.asIdeal) (localPowerSeries f P)



















/-! ### Finite Euler products -/

/-- The part of `f` supported on the nonzero ideals all of whose prime factors lie in `S`: it
agrees with `f` there and vanishes on every other nonzero ideal. Being supported on `S` is
`Ideal.IsPrimeTo · Sᶜ`, that no prime outside `S` divides the ideal. Use
`supportedPart_apply_of_isPrimeTo_compl` and `supportedPart_apply_of_not_isPrimeTo_compl` rather
than unfolding. -/
noncomputable def supportedPart (f : IdealArithmeticFunction K)
    (S : Set (HeightOneSpectrum (𝓞 K))) : IdealArithmeticFunction K :=
  Set.indicator {A : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ} f

variable {f : IdealArithmeticFunction K} {S : Set (HeightOneSpectrum (𝓞 K))}
  {A : (Ideal (𝓞 K))⁰}

omit [NumberField K] in
/-- On an ideal supported on `S`, the restriction of `f` to `S` is `f`. -/
@[simp]
theorem supportedPart_apply_of_isPrimeTo_compl (hA : Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ) :
    supportedPart f S A = f A :=
  Set.indicator_of_mem
    (s := {A : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ}) hA f

omit [NumberField K] in
/-- On an ideal with a prime factor outside `S`, the restriction of `f` to `S` vanishes. -/
@[simp]
theorem supportedPart_apply_of_not_isPrimeTo_compl (hA : ¬ Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ) :
    supportedPart f S A = 0 :=
  Set.indicator_of_notMem
    (s := {A : (Ideal (𝓞 K))⁰ | Ideal.IsPrimeTo (A : Ideal (𝓞 K)) Sᶜ}) hA f



/-- The unit ideal is supported on every set of primes. This is not marked `@[simp]`: `simp`
already reaches it through `supportedPart_apply_of_isPrimeTo_compl`. -/
theorem supportedPart_one (f : IdealArithmeticFunction K) (S : Set (HeightOneSpectrum (𝓞 K))) :
    supportedPart f S 1 = f 1 :=
  supportedPart_apply_of_isPrimeTo_compl (by simp [Ideal.one_eq_top])

/-- Restricting a multiplicative ideal arithmetic function to the ideals supported on `S` keeps it
multiplicative: an ideal is supported on `S` exactly when both factors of a product are. -/
theorem IsMultiplicative.supportedPart (hf : f.IsMultiplicative)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    (IdealArithmeticFunction.supportedPart f S).IsMultiplicative := by
  refine ⟨by rw [supportedPart_one, hf.map_one], fun {I J} hIJ ↦ ?_⟩
  by_cases hI : Ideal.IsPrimeTo (I : Ideal (𝓞 K)) Sᶜ
  · by_cases hJ : Ideal.IsPrimeTo (J : Ideal (𝓞 K)) Sᶜ
    · rw [supportedPart_apply_of_isPrimeTo_compl (A := I * J)
        (by rw [Submonoid.coe_mul]; exact Ideal.isPrimeTo_mul_iff.mpr ⟨hI, hJ⟩),
        supportedPart_apply_of_isPrimeTo_compl hI, supportedPart_apply_of_isPrimeTo_compl hJ,
        hf.map_mul_of_isRelPrime hIJ]
    · rw [supportedPart_apply_of_not_isPrimeTo_compl (A := I * J)
        (by rw [Submonoid.coe_mul, Ideal.isPrimeTo_mul_iff]; tauto),
        supportedPart_apply_of_not_isPrimeTo_compl hJ, mul_zero]
  · rw [supportedPart_apply_of_not_isPrimeTo_compl (A := I * J)
      (by rw [Submonoid.coe_mul, Ideal.isPrimeTo_mul_iff]; tauto),
      supportedPart_apply_of_not_isPrimeTo_compl hI, zero_mul]





















end IdealArithmeticFunction

end TauCeti

end
end


