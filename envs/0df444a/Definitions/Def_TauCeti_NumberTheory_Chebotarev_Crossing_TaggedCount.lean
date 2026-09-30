-- Prove2me | Definitions.Def_TauCeti_NumberTheory_Chebotarev_Crossing_TaggedCount
-- name    : TauCeti_NumberTheory_Chebotarev_Crossing_TaggedCount
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:38:02.836724+00:00
-- url     : https://prove2.me/theorems/c3728136-0e9f-44d8-93b9-fa2e35694758
-- title:
--   Elements with a prescribed divisibility condition on their order
-- statement:
--   For a finite group $H$ and a natural number $f$, define the tagged elements by
--
--   $$
--   T_f(H)=\{h\in H:f\mid\operatorname{ord}(h)\}.
--   $$
--
--   These elements index the auxiliary classes in the cyclotomic crossing argument.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/Crossing/TaggedCount.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/Crossing/TaggedCount.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
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
# Elements with a prescribed divisibility condition on their order

In the cyclic auxiliary group used by the Chebotarev crossing, the useful tags are the elements
whose order is divisible by the order of the chosen Frobenius element. This file gives that finite
carrier together with its membership and divisibility API.

## Main definitions

* `TauCeti.NumberField.Chebotarev.taggedElements`: elements whose order is divisible by a given
  natural number.

## Main results

* `TauCeti.NumberField.Chebotarev.mem_taggedElements_iff`: the defining membership condition.
* `TauCeti.NumberField.Chebotarev.taggedElements_subset_of_dvd`: divisibility makes the tag carrier
  shrink.
* `TauCeti.NumberField.Chebotarev.card_taggedElements_eq_sum_totient`: the exact cyclic count,
  expressed as a sum of Euler totients over the allowed orders.
* `TauCeti.NumberField.Chebotarev.card_taggedElements_cyclic`: the exact count as `#H` times an
  Euler product over the primes of `f`, over `ℝ`.
* `TauCeti.NumberField.Chebotarev.le_card_taggedElements_cyclic`: a uniform lower bound for that
  count, over `ℝ`.

## References

The crossing construction follows R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
-/

 section

open scoped BigOperators

namespace TauCeti.NumberField.Chebotarev

open Finset Nat

/-- The elements of a finite group whose order is divisible by `f`.

The carrier is deliberately a `Finset`, so the tags can be indexed by their order. -/
noncomputable def taggedElements {H : Type*} [Group H] [Fintype H] (f : ℕ) : Finset H :=
  Finset.univ.filter fun τ ↦ f ∣ orderOf τ













end TauCeti.NumberField.Chebotarev

end
end


