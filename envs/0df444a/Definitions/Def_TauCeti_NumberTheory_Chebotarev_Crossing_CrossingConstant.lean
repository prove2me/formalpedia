-- Prove2me | Definitions.Def_TauCeti_NumberTheory_Chebotarev_Crossing_CrossingConstant
-- name    : TauCeti_NumberTheory_Chebotarev_Crossing_CrossingConstant
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:43:40.842023+00:00
-- url     : https://prove2.me/theorems/e81688da-7f36-495c-9553-959d03cc2f67
-- title:
--   The crossing constant of an auxiliary cyclic group
-- statement:
--   For a field extension $L/K$ whose automorphism group is finite, a finite auxiliary group $H$, and $f\in\mathbb N$, the crossing constant is
--
--   $$
--   \frac{\#\{h\in H:f\mid\operatorname{ord}(h)\}}{\#\operatorname{Aut}_K(L)\,\#H}.
--   $$
--
--   It normalizes the number of tags by the sizes of the relevant groups. The formal definition also allows an infinite automorphism group: its natural-number cardinal is then zero, and totalized division makes the crossing constant zero.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/Crossing/CrossingConstant.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/Crossing/CrossingConstant.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_Crossing_TaggedCount
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The crossing constant of an auxiliary cyclic group

The cyclotomic crossing bounds the density of a Frobenius fibre from below by a quantity built
from one auxiliary prime: the proportion of the auxiliary cyclic group `H` taken up by the tags —
the elements whose order is divisible by the residue degree `f` — divided in addition by the order
of `Aut_K(L)`.  Equivalently it is the proportion of `Aut_K(L) × H` represented by one
automorphism paired with the tags.  This file defines that quantity, `crossingConstant`, and
bounds it below.

What the bound provides is uniformity: it depends on `f` only through the number of primes
dividing `f`, and on the auxiliary group only through the level `r` in `f ^ r ∣ #H`, so a consumer
that can raise `r` gets a bound approaching `1 / #Aut_K(L)` without revisiting this file.

## Main definitions

* `TauCeti.NumberField.Chebotarev.crossingConstant`: the tag proportion in `H`, divided by the
  order of `Aut_K(L)`.

## Main results

* `TauCeti.NumberField.Chebotarev.crossingConstant_nonneg`: the constant is nonnegative.
* `TauCeti.NumberField.Chebotarev.le_crossingConstant`: once `f ^ r` divides `#H`, the crossing
  constant is at least `(1 - 2 ^ (-r)) ^ #f.primeFactors` divided by the order of `Aut_K(L)`.

## References

The crossing construction follows R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
-/

 section

namespace TauCeti.NumberField.Chebotarev

open Finset

variable (K L : Type*) [CommSemiring K] [Semiring L] [Algebra K L]
variable {H : Type*} [Group H] [Fintype H]

/-- **The crossing constant.**  The number of tagged elements of the auxiliary cyclic group `H` —
those whose order is divisible by `f` — divided by `#Aut_K(L) * #H`.

That is the tag proportion within `H`, divided in addition by the order of `Aut_K(L)`, which
enters only through its order: the denominator that turns a count of tags into the density
contributed by one auxiliary prime. -/
noncomputable def crossingConstant (f : ℕ) : ℝ :=
  ((taggedElements (H := H) f).card : ℝ) /
    ((Nat.card (L ≃ₐ[K] L) : ℝ) * (Nat.card H : ℝ))







end TauCeti.NumberField.Chebotarev

end
end


