-- Prove2me | Definitions.Def_TauCeti_NumberTheory_RamificationInertia_Tower
-- name    : TauCeti_NumberTheory_RamificationInertia_Tower
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:58:34.810092+00:00
-- url     : https://prove2.me/theorems/dd87f7f8-4844-4b5f-a63b-9de4c66b27f6
-- title:
--   Ramification indices in finite flat towers
-- statement:
--   In a tower of rings $A\to R\to S$ under the stated finiteness and torsion-freeness assumptions, if an ideal of $A$ is unramified in $S$, then every prime of $R$ above it is unramified over $A$. This supplies descent of unramifiedness through an intermediate ring.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/RamificationInertia/Tower.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/RamificationInertia/Tower.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.RamificationInertia.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Ramification indices in finite flat towers

This file records consequences of the fundamental identity for ramification and inertia in a finite
flat extension of domains. The number of primes above a prime and each prime's contribution are at
most the rank of the extension. Ramification also cancels in a tower when the absolute ramification
index at the top equals the absolute ramification index at the intermediate prime: multiplicativity
then forces the relative ramification index to be one.

The cancellation result is the local step used in the finite-place half of the genus-field
construction. At a rational prime dividing a prime discriminant, both the quadratic base and the
prime-discriminant compositum have absolute ramification index two; cancellation then shows that
the compositum is unramified over the quadratic base.

## Main results

* `TauCeti.RamificationInertia.ncard_primesOver_le_finrank`: the number of primes above a prime is
  at most the rank of a finite flat extension.
* `TauCeti.RamificationInertia.ramificationIdx_mul_inertiaDeg_le_finrank`: the contribution of one
  prime to the fundamental identity is at most the rank of the extension.
* `TauCeti.RamificationInertia.ramificationIdx_le_finrank`: a ramification index is at most the
  rank of a finite flat extension.
* `TauCeti.RamificationInertia.ramificationIdx_eq_one_of_eq_ramificationIdx`: equal absolute
  ramification indices at two levels of a tower force relative ramification index one.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_eq_ramificationIdx`: if that equality
  holds at every prime above an intermediate prime, then the intermediate prime is unramified in
  the top ring.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_ramificationIdx_le`: it suffices to bound
  every absolute ramification index upstairs by the intermediate absolute ramification index.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_finrank_le_of_under_ramificationIdx_eq_one`: a
  transverse unramified subextension of sufficiently small relative degree supplies that bound.
* `TauCeti.RamificationInertia.isUnramifiedAt_of_isUnramifiedIn`: unramifiedness over the
  base descends from an integral extension to the subring below it, for `S` integral and
  torsion-free over the Dedekind domain `R`, with `R` and `S` both essentially of finite type over
  the base `A` and `A ≤ R ≤ S` a scalar tower. The base ring and the ideal are arbitrary.
-/

 section

open Ideal Module

namespace TauCeti.RamificationInertia

section Bounds

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Flat R S]







end Bounds

section Tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Module.Finite R S] [Module.Flat S T]









end Tower

section Descent

variable {A R S : Type*} [CommRing A] [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDomain S]
  [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S] [Algebra.IsIntegral R S]
  [Module.IsTorsionFree R S] [Algebra.EssFiniteType A R] [Algebra.EssFiniteType A S]

-- Source. Recovered from the retired PR #5538, at commit
-- 70421db267d9bd6252256f873d27e99e739a931c.

/-- **Unramifiedness descends to a subring.** If an ideal `I` of the base `A` is unramified in `S`,
then every prime of an intermediate ring `R` lying over `I` is unramified over `A`. The direction
is descent, not ascent: the hypothesis is upstairs and the conclusion downstairs.

`A` and `I` are arbitrary; the hypotheses that carry the argument are the ambient ones on `R` and
`S`. Its number-field instance is `NumberField.isUnramifiedAway_of_intermediateField`, which
quantifies it over the places outside a finite set. -/
theorem isUnramifiedAt_of_isUnramifiedIn {I : Ideal A} (hur : Algebra.IsUnramifiedIn S I)
    (𝔮 : Ideal R) [𝔮.IsPrime] [𝔮.LiesOver I] :
    Algebra.IsUnramifiedAt A 𝔮 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (𝔮.primesOver S))
  have : (P : Ideal S).IsPrime := P.2.1
  have : (P : Ideal S).LiesOver 𝔮 := P.2.2
  have : (P : Ideal S).LiesOver I := Ideal.LiesOver.trans (P : Ideal S) 𝔮 I
  have : Algebra.IsUnramifiedAt A (P : Ideal S) := hur (P : Ideal S) ‹_› ‹_›
  exact Algebra.IsUnramifiedAt.of_liesOver A 𝔮 (P : Ideal S)

end Descent

end TauCeti.RamificationInertia

end
end


