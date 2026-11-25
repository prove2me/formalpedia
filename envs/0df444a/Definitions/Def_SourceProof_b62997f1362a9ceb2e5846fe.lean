-- Prove2me | Definitions.Def_SourceProof_b62997f1362a9ceb2e5846fe
-- name    : SourceProof_b62997f1362a9ceb2e5846fe
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:57.45889+00:00
-- url     : https://prove2.me/theorems/c298361c-834f-48bd-bda7-e4ece6439910
-- title:
--   StochLean source theorem: StochLean.pointAtomicPart_apply_eq_tsum

import Definitions.Def_SourceProof_3b0f7c2a9d38ed7556f52fb8

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The point-atomic and point-diffuse parts of an s-finite measure

The countable set of positive-mass singletons is intrinsic. Restriction to it
and to its complement gives the decomposition. On general measurable spaces,
having no point atoms is not asserted to exclude all nonsingleton atoms.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace StochLean

variable {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]

theorem _root_.Prove2MeSourceProof.h_b62997f1362a9ceb2e5846fe (μ : Measure T) [SFinite μ]
    {s : Set T} (hs : MeasurableSet s) :
    pointAtomicPart μ s = ∑' t : s, μ {(t : T)} := by
  classical
  have hsupport : Function.support (s.indicator fun t ↦ μ {t}) ⊆ s ∩ StochLean.pointAtomSet μ := by
    intro t ht
    have hmem : t ∈ s := by
      by_contra h
      exact ht (indicator_of_notMem h _)
    refine ⟨hmem, ?_⟩
    simpa only [StochLean.pointAtomSet, mem_ofPred_eq, Function.mem_support, indicator_of_mem hmem] using ht
  calc
    _ = ∑' t : ↥(s ∩ StochLean.pointAtomSet μ), μ {(t : T)} := _root_.Prove2MeSourceProof.h_3b0f7c2a9d38ed7556f52fb8 μ hs
    _ = ∑' t : ↥(s ∩ StochLean.pointAtomSet μ), s.indicator (fun u ↦ μ {u}) t := by
      apply tsum_congr
      intro t
      rw [indicator_of_mem t.2.1]
    _ = ∑' t, s.indicator (fun u ↦ μ {u}) t := tsum_subtype_eq_of_support_subset hsupport
    _ = ∑' t : s, μ {(t : T)} := (tsum_subtype s (fun t ↦ μ {t})).symm
end StochLean


