-- Prove2me | Definitions.Def_TauCeti_RingTheory_DedekindDomain_PrimesAbove
-- name    : TauCeti_RingTheory_DedekindDomain_PrimesAbove
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:42:17.018374+00:00
-- url     : https://prove2.me/theorems/4216938f-cdc4-4208-9e47-edccf455832b
-- title:
--   Primes above a set of primes, and the Selmer group relative to them
-- statement:
--   For an extension of domains $R\subseteq B$, the primes of $B$ above a set $S$ of primes of $R$ are
--
--   $$
--   \{Q:Q\cap R\in S\}.
--   $$
--
--   Under the stated Dedekind and finiteness hypotheses, a finite set has only finitely many primes above it. This construction tracks exceptional primes through extensions.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/DedekindDomain/PrimesAbove.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/DedekindDomain/PrimesAbove.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Primes above a set of primes, and the Selmer group relative to them

For an injective algebra map of commutative rings `R → B` with `B` Dedekind, only finitely
many nonzero prime ideals of `B` lie over a given nonzero prime `v` of `R`. This does not
require integrality or a Dedekind hypothesis on `R`.

For domains `R` and `B` with `B` integral over `R`, contraction defines
`HeightOneSpectrum.under R`. For a set `S` of primes of `R`,
`IsDedekindDomain.HeightOneSpectrum.primesAbove R B S` is its preimage under contraction.
When `B` is Dedekind and the algebra map is injective, this preimage is finite whenever `S` is.
The Selmer group of the fraction field of `B` relative to these primes is
`IsDedekindDomain.selmerGroupAbove R B L S n`, Mathlib's `L⟮primesAbove R B S, n⟯`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.primesAbove`: the primes of `B` above a set of primes
  of `R`, as a preimage under `HeightOneSpectrum.under`.
* `IsDedekindDomain.selmerGroupAbove`: the `n`-Selmer group of `L` relative to the primes of `B`
  above `S`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.liesOver_under`: the `LiesOver` instance relating a prime
  to its contraction, which the `under`-indexed results downstream need.
* `IsDedekindDomain.HeightOneSpectrum.under_under`: contraction through a tower agrees with
  direct contraction.
* `IsDedekindDomain.HeightOneSpectrum.mem_primesAbove_iff`: `w` lies above `S` iff
  `HeightOneSpectrum.under R w ∈ S`.
* `IsDedekindDomain.HeightOneSpectrum.primesAbove_finite`: finitely many primes lie above a
  finite set.
* `IsDedekindDomain.HeightOneSpectrum.tendsto_under_cofinite`: consequently, contraction tends to
  the cofinite filter along the cofinite filter;
  `IsDedekindDomain.HeightOneSpectrum.tendsto_under_cofinite_of_isFractionRing` is the variant
  for rings mapping compatibly to a common nontrivial algebra over a fraction field.
* `IsDedekindDomain.HeightOneSpectrum.finite_liesOver`: finitely many height one primes lie over
  a given one.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, at commit `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`, section `DedekindDomain`. The source carries its own
`HeightOneSpectrum.below`; at our Mathlib pin that map is `HeightOneSpectrum.under`, which is
used here instead.

The source is written against Lean `v4.32.0`; this is a forward port.
-/

 section

namespace IsDedekindDomain

variable (R : Type*) [CommRing R] (B : Type*) [CommRing B] [Algebra R B]

namespace HeightOneSpectrum

section IsDomain

variable [IsDomain R] [IsDomain B] [Algebra.IsIntegral R B]

/-- A height one prime of `B` lies over its own contraction to `R`.

Mathlib's `Ideal.over_under` is this statement for `Ideal.under`, but instance search does not see
through the `HeightOneSpectrum.asIdeal` projection to reach it, so it is registered here. Results
stated at `under R w` and consuming a `LiesOver` hypothesis, such as
`HeightOneSpectrum.valuation_liesOver`, do not fire without it. -/
instance liesOver_under (w : HeightOneSpectrum B) :
    w.asIdeal.LiesOver (under R w).asIdeal :=
  ⟨rfl⟩

section UnderTower

variable {A C : Type*} [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
  [Algebra A R] [Algebra R C] [Algebra A C] [IsScalarTower A R C]
  [Algebra.IsIntegral A R] [Algebra.IsIntegral R C]



end UnderTower

/-- The primes of `B` lying above a set `S` of primes of `R`: the preimage of `S` under the
contraction `HeightOneSpectrum.under R`. -/
def primesAbove (S : Set (HeightOneSpectrum R)) : Set (HeightOneSpectrum B) :=
  under R ⁻¹' S







end IsDomain

section

variable {R B}

variable (B) [FaithfulSMul R B]

/-- Only finitely many nonzero primes of a Dedekind domain `B` lie over a given nonzero
prime of `R`. The extension need not be integral, and `R` need not be Dedekind. -/
instance finite_liesOver [IsDedekindDomain B] (v : HeightOneSpectrum R) :
    Finite {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} := by
  have h := Ideal.finite_factors (Ideal.map_ne_bot_of_ne_bot (S := B) v.ne_bot)
  exact (h.subset fun w hw ↦ Ideal.dvd_iff_le.mpr
    (Ideal.map_le_iff_le_comap.mpr (le_of_eq hw.over))).to_subtype

end

/-- Only finitely many primes of `B` lie above a finite set of primes of `R`. -/
lemma primesAbove_finite [IsDomain R] [IsDedekindDomain B] [Algebra.IsIntegral R B]
    [FaithfulSMul R B] {S : Set (HeightOneSpectrum R)} (hS : S.Finite) :
    (primesAbove R B S).Finite := by
  refine hS.preimage' fun v _ ↦ ?_
  have : Finite (under R (B := B) ⁻¹' {v}) :=
    Finite.of_injective
      (fun w ↦ (⟨w.1, ⟨congrArg asIdeal (Set.mem_singleton_iff.mp w.2).symm⟩⟩ :
        {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}))
      (fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h))
  exact Set.toFinite _





end HeightOneSpectrum

variable [IsDomain R] [IsDedekindDomain B] [Algebra.IsIntegral R B]







end IsDedekindDomain

end

end


