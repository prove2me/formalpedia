-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Cyclotomic_Ramification
-- name    : TauCeti_NumberTheory_NumberField_Cyclotomic_Ramification
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:38:19.428046+00:00
-- url     : https://prove2.me/theorems/8de711f0-5ea6-415e-bb37-5b49e557edc0
-- title:
--   The ramified primes of a cyclotomic extension of a number field
-- statement:
--   In an $m$-th cyclotomic extension of number fields, the level $m$ lies in the different ideal. In particular, primes not dividing $m$ are unramified. This confines the exceptional primes of a cyclotomic extension to its level.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Cyclotomic/Ramification.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Cyclotomic/Ramification.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The ramified primes of a cyclotomic extension of a number field

Let `M / K` be an `m`-th cyclotomic extension with `K` a number field. The level `m` lies in the
different ideal of `𝓞 M` over `𝓞 K` — equivalently, that different divides `(m)` — so
ramification in `M / K` is confined to the primes above `m`. Read through absolute discriminants,
along the factorisation `|discr M| = 𝔑 𝔡(𝓞 M / 𝓞 K) * |discr K| ^ [M : K]`, the same bound says
that a rational prime dividing `discr M` divides `discr K` or divides `m`: the extension ramifies
only below or at the level.

Neither statement constrains `m` against `K`. In that they differ from the degree identity
`[M : K] = φ m` of `TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank`, which needs `m` coprime
to `discr K` and fails outright when `K` already contains a primitive `m`-th root of unity.

## Main results

* `IsCyclotomicExtension.natCast_mem_differentIdeal`: the level `m` lies in the different ideal
  of `𝓞 M` over `𝓞 K`.
* `IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem`: primes above an ideal not
  containing the level are unramified.
* `IsCyclotomicExtension.prime_dvd_natAbs_discr_or_dvd_of_dvd_natAbs_discr`: a prime dividing
  `discr M` divides `discr K` or divides `m` — the extension ramifies only below or at the level.

## Implementation notes

`natCast_mem_differentIdeal` reads as a membership rather than as a divisibility of
`Ideal.span {(m : 𝓞 M)}`; `Ideal.span_singleton_le_iff_mem` gives the divisibility form where
that is the one wanted.

These results ask `M` to be a number field alongside `K`. That is no restriction, since a
cyclotomic extension of a number field is one: `IsCyclotomicExtension.numberField {m} K M`.

-/

 section

namespace IsCyclotomicExtension

open NumberField Polynomial in
/-- **The level lies in the different ideal.** For `M / K` an `m`-th cyclotomic extension of
number fields, `m` belongs to the different ideal of `𝓞 M` over `𝓞 K`; equivalently that different
divides `(m)`, so only primes dividing `m` can ramify in `M / K`. -/
theorem natCast_mem_differentIdeal (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (m : ℕ) [IsCyclotomicExtension {m} K M] :
    (m : 𝓞 M) ∈ differentIdeal (𝓞 K) (𝓞 M) := by
  obtain rfl | hm := Nat.eq_zero_or_pos m
  · -- At level `0` the claim reads `0 ∈ differentIdeal`, and every ideal contains `0`.
    simp
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) K M
    (Set.mem_singleton m) (NeZero.ne m)
  set z : 𝓞 M := hζ.toInteger
  -- `M = K(ζ)` is generated over `K` by a primitive `m`-th root of unity, so the different
  -- contains the element `aeval ζ (derivative (minpoly (𝓞 K) ζ))`.
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 K) K M z
    (IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ)
  have hzpow : z ^ m = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  -- `ζ` is a root of `X ^ m - 1`, so its minimal polynomial divides that.
  obtain ⟨q, hq⟩ : minpoly (𝓞 K) z ∣ (X ^ m - 1 : (𝓞 K)[X]) :=
    minpoly.isIntegrallyClosed_dvd (Algebra.IsIntegral.isIntegral z) (by simp [hzpow])
  -- Differentiating that factorisation at `ζ` makes `m * ζ ^ (m - 1)` a multiple of `hmem`.
  have hder : (m : 𝓞 M) * z ^ (m - 1) =
      aeval z (derivative (minpoly (𝓞 K) z)) * aeval z q := by
    have h : aeval z (derivative (X ^ m - 1 : (𝓞 K)[X])) =
        aeval z (derivative (minpoly (𝓞 K) z * q)) := by rw [hq]
    simpa [derivative_mul, derivative_X_pow, minpoly.aeval] using h
  -- Multiplying by `ζ` and using `ζ ^ m = 1` turns `m * ζ ^ (m - 1)` into `m` itself.
  have hm : (m : 𝓞 M) = aeval z (derivative (minpoly (𝓞 K) z)) * aeval z q * z := by
    rw [← hder, mul_assoc, pow_sub_one_mul (NeZero.ne m) z, hzpow, mul_one]
  rw [hm]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hmem)

open NumberField in
/-- In a cyclotomic extension of level `m`, every prime above an ideal not containing `m`
is unramified. -/
theorem isUnramifiedAt_of_natCast_notMem {K : Type*} [Field K] [NumberField K]
    (F : Type*) [Field F] [NumberField F] [Algebra K F] (m : ℕ)
    [IsCyclotomicExtension {m} K F] {p : Ideal (𝓞 K)} (hm : (m : 𝓞 K) ∉ p)
    (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver p] : Algebra.IsUnramifiedAt (𝓞 K) Q := by
  by_contra hQ
  refine hm ((Ideal.mem_of_liesOver Q p _).mpr ?_)
  simpa using Ideal.le_of_dvd (dvd_differentIdeal_iff.mpr hQ)
    (natCast_mem_differentIdeal K F m)



end IsCyclotomicExtension

end
end


