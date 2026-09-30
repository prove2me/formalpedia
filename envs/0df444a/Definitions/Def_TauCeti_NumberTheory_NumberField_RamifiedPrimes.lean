-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_RamifiedPrimes
-- name    : TauCeti_NumberTheory_NumberField_RamifiedPrimes
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:56:51.988652+00:00
-- url     : https://prove2.me/theorems/8c8eba7e-c3fa-4517-924e-5e32dca50607
-- title:
--   The ramified rational primes of a number field
-- statement:
--   For a number field $K$, the ramified rational primes are the natural primes $p$ for which the ideal $(p)\subseteq\mathbb Z$ ramifies in $\mathcal O_K$. This is the absolute ramification set used when choosing auxiliary primes.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/RamifiedPrimes.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/RamifiedPrimes.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.ExistsRamified

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The ramified rational primes of a number field

The genus theory of a quadratic field is governed by the number `t` of rational primes that ramify
in it: the genus field has degree `2 ^ t` over `ℚ` and the `2`-rank of the narrow class group is
`t - 1`. This file names that set of primes and records its basic properties.

Mathlib phrases ramification of a rational prime `p` in a number field `K` as
`Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})`, and characterises it by divisibility of the
discriminant (`NumberField.not_dvd_discr_iff_isUnramifiedIn`). We package the negation as a set of
natural primes, which is the form in which `t` is counted.

## Main definitions

* `NumberField.ramifiedPrimes`: the set of natural primes ramifying in `K`.

## Main results

* `NumberField.mem_ramifiedPrimes_iff_dvd_discr`: a prime ramifies iff it divides the
  discriminant.
* `NumberField.coprime_natAbs_discr_of_isUnramifiedIn`: an unramified prime is coprime to the
  discriminant.
* `AlgEquiv.ramifiedPrimes_eq`: isomorphic number fields have the same ramified primes.
* `NumberField.ramifiedPrimes_rat`: no prime ramifies in `ℚ`.
* `NumberField.finite_ramifiedPrimes`: only finitely many primes ramify.
* `NumberField.ramifiedPrimes_nonempty`: some prime ramifies, unless `K = ℚ`
  (Minkowski, via `NumberField.exists_not_isUnramifiedIn`).
-/

 section

open scoped NumberField

namespace NumberField

variable (K : Type*) [Field K]

/-- **The ramified rational primes of a number field.** The set of natural primes `p` such that
`p` — as the ideal `span {p}` of `ℤ` — ramifies in the ring of integers of `K`. For a quadratic
field `K`, its cardinality is the `t` of genus theory. -/
def ramifiedPrimes : Set ℕ :=
  {p | p.Prime ∧ ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})}

variable {K}





variable [NumberField K]







-- Source. The hypothesis this discharges is
-- `hcop : ((NumberField.discr L).natAbs).Coprime m` in the Birkbeck--Brasca Chebotarev
-- development, CBirkbeck/chebotarev-density (Apache-2.0), branch `development` at
-- `8575c9df1ae0a61120ab5c964c7911414254bec7`. There `CebotarevDensity/Abelian.lean` carries it
-- undischarged throughout, obtaining `p ∤ discr E` from
-- `NumberField.not_dvd_discr_iff_forall_liesOver` inline. The statement below is that hypothesis;
-- deriving it from `Algebra.IsUnramifiedIn` is not done in the source, which propagates it.







end NumberField

end
end


