-- Prove2me | Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
-- name    : TauCeti_RingTheory_DedekindDomain_Ideal
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:37:55.04765+00:00
-- url     : https://prove2.me/theorems/e9163ef7-dd59-4751-acf7-0dc7a55af6e4
-- title:
--   Complements on ideals of a Dedekind domain
-- statement:
--   Let $R$ be a Dedekind domain and $S$ a set of its nonzero prime ideals. An ideal $I$ is prime to $S$ when
--
--   $$
--   I\ne0\quad\text{and}\quad P\nmid I\text{ for every }P\in S.
--   $$
--
--   The bundle supplies multiplicativity and ideal-factorization properties of this condition, used to exclude Euler factors.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/DedekindDomain/Ideal.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/DedekindDomain/Ideal.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Complements on ideals of a Dedekind domain

This file collects general facts about ideals and height-one primes of a Dedekind domain,
complementing `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`. In particular, it develops
the predicate `Ideal.IsPrimeTo I S`, saying that `I` is nonzero and divisible by no prime in `S`,
together with its induction principle `Ideal.IsPrimeTo.induction_on` and its transport
`Ideal.isPrimeTo_comap_iff` along a ring isomorphism.

The predicate is closed under products (`Ideal.isPrimeTo_mul_iff`, its finite form
`Ideal.isPrimeTo_prod_iff`) and powers (`Ideal.isPrimeTo_pow_iff`), and forbidding one more
prime is `Ideal.isPrimeTo_insert_iff`. Complementing a set of primes
turns it into a *support* condition: `IsPrimeTo I Sᶜ` says that every prime factor of `I` lies in
`S`. The two extreme cases are `Ideal.isPrimeTo_univ_iff` (no prime factor at all, so `I = ⊤`) and
`Ideal.isPrimeTo_compl_singleton_iff` (a single allowed prime, so `I` is a prime power), and
`Ideal.IsPrimeTo.exists_eq_pow_mul` splits off one allowed prime at a time. The file also records
the prime-power factorization `Ideal.exists_eq_prod_pow` of an arbitrary nonzero ideal. Together
with the uniqueness statement `Ideal.eq_and_eq_of_pow_mul_eq_pow_mul` and the relative primality
`Ideal.IsPrimeTo.isRelPrime` of ideals supported on complementary sets, these are what turn a
finite set of primes into a finite Euler product in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Basic.lean`.

It also collects how an isomorphism `e : R ≃+* R'` moves ideals: `Ideal.map e` preserves
divisibility (`Ideal.map_dvd_map_iff_of_ringEquiv`, `Ideal.map_pow_dvd_map_iff_of_ringEquiv`,
stated over commutative *semirings*, since the proofs use only that `Ideal.map e` and
`Ideal.map e.symm` are mutually inverse) and factorisation multiplicities
(`Ideal.count_factors_map_of_ringEquiv`), and Mathlib's transport `equivOfRingEquiv e` of height
one primes is `Ideal.map e` on underlying ideals
(`IsDedekindDomain.HeightOneSpectrum.asIdeal_equivOfRingEquiv`). Those four are the ideal-level
input to the adic-valuation transport in
`TauCeti/RingTheory/DedekindDomain/AdicValuation/Transport.lean`; they are adapted from
[AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Apache-2.0), commit `513e83879e2f`,
`projects/HasseWeil/HasseWeil/WeilPairing/DivisorGalois.lean`.

`Ideal.IsPrimeTo` generalizes the `IsGood` predicate of
`TauCetiRoadmap/ArithmeticDirichletSeries/Suggested.lean`, where it is stated for the bad primes
of an ideal weight on a number field; the design of the predicate — nonzeroness included, so that
`⊥` is prime to no set at all — is taken from there, while nothing in it is specific to a number
field.

The file also identifies any height-one prime of a discrete valuation ring with its maximal ideal
(`IsDedekindDomain.HeightOneSpectrum.eq_maximalIdeal`), which is what lets a condition stated at
the height-one primes of such a ring be read as a condition on its valuation. It was split out of
material adapted from Michael Stoll's elliptic-curves formalisation
(`EllipticCurves/Mathlib/AdicCompletionExtension.lean` at the roadmap's pin `66889eada51a`,
Apache 2.0, by Michael Stoll), where it is the step behind `valuation_adicCompletion_algebraMap`.

The theorem `IsDedekindDomain.HeightOneSpectrum.exists_mem_notMem` was split out of material
adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SIntegers.lean` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll); following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.

`IsDedekindDomain.HeightOneSpectrum.comapOfNeBot` and its projection are likewise adapted from that
formalisation (`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/Basic.lean`
line 539, at the roadmap's pin `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, Apache 2.0, by Michael
Stoll). The construction is the source's; what changed is the hypothesis — the source and this
version take the nonvanishing of the contraction as a hypothesis, where Mathlib's
`HeightOneSpectrum.comap` instead derives it from surjectivity of the map.

`Ideal.ne_bot_of_comap_ne_bot` plays the role of the source's
`comap_ne_bot_of_comap_comap_ne_bot` (`EllipticCurves/Mathlib/Basic.lean` line 270): it is what
discharges that nonvanishing hypothesis when a prime is contracted through an intermediate ring.
It is stated here in the general form — an arbitrary ideal and an injective ring homomorphism,
with the map producing the ideal dropped, since it plays no role — and proved from Mathlib's
`Ideal.comap_bot_of_injective`.
-/

 section

namespace Ideal

section CommSemiring

variable {R R' : Type*} [CommSemiring R] [CommSemiring R']





end CommSemiring

section RingEquivDedekind

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']



end RingEquivDedekind

section Multiplicity

variable {B : Type*} [CommRing B] [IsDedekindDomain B]



end Multiplicity

section Injective



end Injective

end Ideal

namespace IsDedekindDomain.HeightOneSpectrum

section Comap

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]





end Comap

section RingEquivTransport

variable {R R' : Type*} [CommRing R] [CommRing R']



end RingEquivTransport

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]



end IsDedekindDomain.HeightOneSpectrum

namespace Ideal

-- `_root_` disambiguates: inside `namespace Ideal`, a bare `open IsDedekindDomain` would resolve
-- to the `Ideal.IsDedekindDomain` namespace of Mathlib's ramification indices, which the
-- `Factorization` import above makes visible here.
open _root_.IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- An ideal of a Dedekind domain is **prime to** a set `S` of height-one primes when it is
nonzero and no prime of `S` divides it. Nonzeroness is part of the definition, so `⊥` is prime
to no set at all — not even to `∅`. -/
def IsPrimeTo (I : Ideal R) (S : Set (HeightOneSpectrum R)) : Prop :=
  I ≠ ⊥ ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I

variable {I J : Ideal R} {S T : Set (HeightOneSpectrum R)}

omit [IsDedekindDomain R] in
theorem isPrimeTo_iff : IsPrimeTo I S ↔ I ≠ ⊥ ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I := Iff.rfl

omit [IsDedekindDomain R] in
theorem IsPrimeTo.ne_bot (h : IsPrimeTo I S) : I ≠ ⊥ := h.1

omit [IsDedekindDomain R] in
theorem IsPrimeTo.not_dvd (h : IsPrimeTo I S) {𝔭 : HeightOneSpectrum R} (h𝔭 : 𝔭 ∈ S) :
    ¬ 𝔭.asIdeal ∣ I := h.2 𝔭 h𝔭

omit [IsDedekindDomain R] in
/-- The zero ideal is prime to no set of primes, not even to the empty set. -/
@[simp]
theorem not_isPrimeTo_bot : ¬ IsPrimeTo (⊥ : Ideal R) S := fun h ↦ h.ne_bot rfl



@[simp]
theorem isPrimeTo_top : IsPrimeTo (⊤ : Ideal R) S := by
  refine ⟨top_ne_bot, fun 𝔭 _ hdvd ↦ 𝔭.prime.not_isUnit ?_⟩
  exact isUnit_of_dvd_one (by simpa [Ideal.one_eq_top] using hdvd)





/-- **Being prime to `S` is multiplicative.** A product of ideals is prime to `S` exactly when
both factors are: neither factor may vanish, and a prime of `S` divides the product exactly when
it divides one of the factors. -/
@[simp]
theorem isPrimeTo_mul_iff : IsPrimeTo (I * J) S ↔ IsPrimeTo I S ∧ IsPrimeTo J S := by
  simp only [IsPrimeTo, ne_eq, Ideal.mul_eq_bot, not_or]
  refine ⟨fun ⟨h0, h⟩ ↦ ⟨⟨h0.1, fun 𝔭 h𝔭 hdvd ↦ h 𝔭 h𝔭 (hdvd.mul_right _)⟩,
    ⟨h0.2, fun 𝔭 h𝔭 hdvd ↦ h 𝔭 h𝔭 (hdvd.mul_left _)⟩⟩, fun ⟨hI, hJ⟩ ↦ ⟨⟨hI.1, hJ.1⟩, ?_⟩⟩
  intro 𝔭 h𝔭 hdvd
  rcases 𝔭.prime.dvd_mul.mp hdvd with h | h
  · exact hI.2 𝔭 h𝔭 h
  · exact hJ.2 𝔭 h𝔭 h

/-- A height-one prime ideal is prime to `S` exactly when its spectrum point is not in `S`. -/
@[simp]
theorem isPrimeTo_asIdeal_iff {𝔭 : HeightOneSpectrum R} :
    IsPrimeTo 𝔭.asIdeal S ↔ 𝔭 ∉ S := by
  refine ⟨fun h h𝔭 ↦ h.not_dvd h𝔭 dvd_rfl, fun h𝔭 ↦ ⟨𝔭.ne_bot, fun 𝔮 h𝔮 hdvd ↦ h𝔭 ?_⟩⟩
  exact HeightOneSpectrum.asIdeal_injective
    ((prime_dvd_prime_iff_eq 𝔮.prime 𝔭.prime).mp hdvd) ▸ h𝔮



/-- **Induction on ideals prime to `S`.** Such an ideal is a finite product of height-one
primes outside `S`, so a property holding at `⊤` and stable under multiplication by a
height-one prime outside `S` holds for all of them. -/
@[elab_as_elim]
theorem IsPrimeTo.induction_on {motive : Ideal R → Prop} (h : IsPrimeTo I S)
    (top : motive ⊤)
    (mul_prime : ∀ (𝔭 : HeightOneSpectrum R) (J : Ideal R), 𝔭 ∉ S →
      IsPrimeTo J S → motive J → motive (𝔭.asIdeal * J)) :
    motive I := by
  revert h
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h ↦ absurd rfl h.ne_bot
  | h₂ x hx => exact fun _ ↦ (Ideal.isUnit_iff.mp hx) ▸ top
  | h₃ J p _ hp ih =>
      intro hprime
      have hJ : IsPrimeTo J S := (isPrimeTo_mul_iff.mp hprime).2
      have hbad : HeightOneSpectrum.ofPrime hp ∉ S :=
        fun h ↦ hprime.2 _ h (dvd_mul_right p J)
      exact mul_prime (HeightOneSpectrum.ofPrime hp) J hbad hJ (ih hJ)





















end Ideal

section DiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum



end IsDedekindDomain.HeightOneSpectrum

end DiscreteValuationRing

end

end


