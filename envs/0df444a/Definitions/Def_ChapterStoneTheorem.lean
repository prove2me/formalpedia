-- Prove2me | Definitions.Def_ChapterStoneTheorem
-- name    : ChapterStoneTheorem
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:54:03.493605+00:00
-- url     : https://prove2.me/theorems/dabf456e-77cb-414c-9ea1-3b747a3a7b55
-- title:
--   This file assembles the two halves of Stone's theorem proved in `ChapterStoneResolvent`–`ChapterStoneConverse` into a si ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.StoneTheorem`, source chapter `BookProof/ChapterStoneTheorem.lean`).
--
--   This file assembles the two halves of Stone's theorem proved in `ChapterStoneResolvent`–`ChapterStoneConverse` into a single statement.
--
--   * **Forward direction.** Every unbounded self-adjoint operator `A` (with dense domain) on a complex Hilbert space generates a one-parameter unitary group `e^{-itA}` (`UnboundedSelfAdjoint.stoneGroup`), which is even strongly continuous, hence weakly measurable, and solves the Schrödinger equation on the domain of `A`. * **Converse direction.** On a *separable* Hilbert space, every weakly measurable one-parameter unitary group `U` is of this form: its infinitesimal generator `A` is self-adjoint and `U t = e^{-itA}` (`WeakMeasurableUnitaryGroup.gen_stoneU_eq`). * **Uniqueness.** The generator of `e^{-itA}` is again `A` (`UnboundedSelfAdjoint.gen_stoneGroup_eq`), so the two constructions are mutually inverse (`BookProof.ChapterStoneTheorem.stone_bijection`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStoneTheorem.lean

import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneEvolution
import Definitions.Def_ChapterStoneGenerator
import Definitions.Def_ChapterStoneGroup
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterUnitaryTransport

import Mathlib

import Mathlib
open BookProof.ChapterUnitaryTransport
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneResolvent

/-!
# The general Stone theorem on a separable Hilbert space

This file assembles the two halves of Stone's theorem proved in
`ChapterStoneResolvent`–`ChapterStoneConverse` into a single statement.

* **Forward direction.**  Every unbounded self-adjoint operator `A` (with dense domain)
  on a complex Hilbert space generates a one-parameter unitary group `e^{-itA}`
  (`UnboundedSelfAdjoint.stoneGroup`), which is even strongly continuous, hence weakly
  measurable, and solves the Schrödinger equation on the domain of `A`.
* **Converse direction.**  On a *separable* Hilbert space, every weakly measurable
  one-parameter unitary group `U` is of this form: its infinitesimal generator `A` is
  self-adjoint and `U t = e^{-itA}` (`WeakMeasurableUnitaryGroup.gen_stoneU_eq`).
* **Uniqueness.**  The generator of `e^{-itA}` is again `A`
  (`UnboundedSelfAdjoint.gen_stoneGroup_eq`), so the two constructions are mutually
  inverse (`BookProof.ChapterStoneTheorem.stone_bijection`).
-/

open scoped InnerProductSpace

namespace BookProof.ChapterStoneMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]



end BookProof.ChapterStoneMeasurable

namespace BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



/-! ## The forward direction: a self-adjoint operator generates a unitary group -/

/-- **Stone's theorem, forward direction.**  A self-adjoint operator `A` generates a
one-parameter unitary group `t ↦ e^{-itA}`, which is weakly measurable (indeed strongly
continuous, see `UnboundedSelfAdjoint.continuous_stoneU_apply`). -/
noncomputable def stoneGroup (T : UnboundedSelfAdjoint H) : WeakMeasurableUnitaryGroup H where
  U := T.stoneU
  map_zero := T.stoneU_zero
  map_add := T.stoneU_add
  norm_map := T.norm_stoneU_apply
  weaklyMeasurable := fun x y => T.measurable_inner_stoneU x y



/-! ## The generator of `e^{-itA}` is `A` -/







variable [TopologicalSpace.SeparableSpace H]



end BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint

namespace BookProof.ChapterStoneTheorem


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]



end BookProof.ChapterStoneTheorem


