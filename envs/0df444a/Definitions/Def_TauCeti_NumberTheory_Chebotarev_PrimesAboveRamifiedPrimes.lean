-- Prove2me | Definitions.Def_TauCeti_NumberTheory_Chebotarev_PrimesAboveRamifiedPrimes
-- name    : TauCeti_NumberTheory_Chebotarev_PrimesAboveRamifiedPrimes
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:51:23.766915+00:00
-- url     : https://prove2.me/theorems/a9f01168-8c39-429b-a5f3-50c4cd0ae0e5
-- title:
--   The primes of a number field above those ramifying in another
-- statement:
--   For extensions $E/K$ and $L/K$ of number fields, define the primes of $E$ above the ramified primes of $L/K$ by
--
--   $$
--   \{Q\subseteq\mathcal O_E:Q\cap\mathcal O_K\in\operatorname{Ram}(L/K)\}.
--   $$
--
--   This tracks the exceptional primes after changing the field in which primes are counted.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimesAboveRamifiedPrimes.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimesAboveRamifiedPrimes.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_PrimesAbove
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_RamificationLocus
import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Separable
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Unramified.Locus

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The primes of a number field above those ramifying in another

For an extension `L / K` of number fields and a further number field `E` over `K`, this file
collects the height-one primes of `𝓞 E` whose contraction to `𝓞 K` ramifies in `L`. There are
finitely many, so they form a `Finset`.

`E` is unrelated to `L`: the condition constrains the prime of `K` below, and says nothing about
how the prime behaves in `L / E`.

## Main definitions

* `NumberField.Chebotarev.primesAboveRamifiedPrimes`: the finite set of height-one primes of
  `𝓞 E` lying above `ramifiedPrimes K L`.

## Main results

* `NumberField.Chebotarev.mem_primesAboveRamifiedPrimes_iff`: the defining condition for
  membership.
* `NumberField.Chebotarev.under_mem_primesAboveRamifiedPrimes_of_not_isUnramifiedAt`: a prime
  below a ramified prime in a tower satisfies the defining condition.
* `NumberField.Chebotarev.under_mem_primesAboveRamifiedPrimes_iff_inertia_ne_bot`: in a
  Galois tower, membership of the contraction is equivalent to nontrivial inertia upstairs.

## Comparison with ramification in `L / E`

Nothing here assumes `E` embeds in `L`, so in general there is no ramification in `L / E` to
compare against: membership is a condition on the prime of `K` below `𝔓`, and nothing else.

When a compatible tower `K → E → L` does exist, the two conditions are still not the same one.
Ramification indices multiply along a tower, `e(Q/𝔭) = e(Q/𝔓) · e(𝔓/𝔭)`, so a prime of `E`
ramifying in `L / E` always lies in this set. The inclusion can be strict, and that is why the
condition is imposed below rather than on `L / E`.

For example, take `K = ℚ` and `L = ℚ(∛2, ζ₃)`, so that `Gal(L/K) ≅ S₃`; let `E = ℚ(∛2)`, the field
fixed by a transposition, and let `p = 2`. The inertia group at a prime `Q` of `L` above `2` is the
cyclic group of order three, so `e(Q/2) = 3` while `e(Q/𝔓) = 1`: all of the ramification,
`e(𝔓/2) = 3`, happens below `E`. So `𝔓` is unramified in `L / E` and yet lies above a prime
ramifying in `L / K` — a witness that the inclusion is strict here.

## References

Adapted from `ramifiedBelow_finite` in `CebotarevDensity/FixedFieldDensity.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) on branch `development` at commit
`8575c9df1ae0a61120ab5c964c7911414254bec7`, where the set appears for `E` the fixed field of a
cyclic subgroup of `Gal(L/K)`.
-/

 section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable (K L E : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field E] [NumberField E] [Algebra K E]

/-- **The primes of `E` above those of `K` ramifying in `L`.** The height-one primes of `𝓞 E`
whose contraction to `𝓞 K` lies in `ramifiedPrimes K L`.

The condition is on the prime of `K` below. It is not ramification in `L / E`, which need not
even be defined here; the module docstring compares the two when a tower exists. -/
noncomputable def primesAboveRamifiedPrimes : Finset (HeightOneSpectrum (𝓞 E)) :=
  (HeightOneSpectrum.primesAbove_finite (𝓞 K) (𝓞 E)
    (ramifiedPrimes K L).finite_toSet).toFinset

variable {K L E}







end NumberField.Chebotarev

end
end


