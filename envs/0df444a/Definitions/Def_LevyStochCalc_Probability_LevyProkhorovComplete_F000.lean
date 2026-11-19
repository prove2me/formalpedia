-- Prove2me | Definitions.Def_LevyStochCalc_Probability_LevyProkhorovComplete_F000
-- name    : LevyStochCalc_Probability_LevyProkhorovComplete_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:29:08.650363+00:00
-- url     : https://prove2.me/theorems/9d078097-1bb4-4624-aa6b-019adf73c6f1
-- title:
--   Source declarations: LevyStochCalc.Probability.LevyProkhorovComplete
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.LevyProkhorovComplete. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_c96b33d6be4a8e5dc0e21209
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Completeness of the Lévy–Prokhorov metric

On a proper metric space `Ω` (for instance `ℝ` or `ℝⁿ`) with its Borel σ-algebra, the
Lévy–Prokhorov metric on probability measures is complete.

A totally bounded set of probability measures is tight: take a finite `ε/2`-net, a compact set `K`
carrying all but `ε/2` of the mass of each net point, and the closed `ε/2`-thickening of `K`, which
is compact because `Ω` is proper; the Lévy–Prokhorov thickening inequality transfers the mass bound
from each net point to every measure near it. By Prokhorov's theorem a tight set has compact
closure, so the range of a Cauchy sequence is relatively compact and the sequence converges.

## Main statements

* `LevyStochCalc.Probability.isTightMeasureSet_of_totallyBounded` — a totally bounded set of
  probability measures is tight.
* `LevyStochCalc.Probability.isCompact_closure_of_isTightMeasureSet_levyProkhorov` — Prokhorov's
  theorem in the Lévy–Prokhorov metric: a tight set has compact closure.
* `LevyStochCalc.Probability.instCompleteSpaceLevyProkhorovProbabilityMeasure` — the
  Lévy–Prokhorov metric space of probability measures is complete.
-/

open MeasureTheory Filter Set Topology TopologicalSpace
open scoped ENNReal

namespace LevyStochCalc.Probability

variable {Ω : Type*} [MetricSpace Ω] [ProperSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]

omit [ProperSpace Ω] in
/-- Prokhorov's theorem in the Lévy–Prokhorov metric: on a separable metric space, a tight set of
probability measures has compact closure. -/
theorem isCompact_closure_of_isTightMeasureSet_levyProkhorov [SeparableSpace Ω]
    (S : Set (LevyProkhorov (ProbabilityMeasure Ω)))
    (htight : IsTightMeasureSet {(μ.toMeasure.toMeasure : Measure Ω) | μ ∈ S}) :
    IsCompact (closure S) := by
  set h := LevyProkhorov.probabilityMeasureHomeomorph (Ω := Ω) with hh
  have hST : h '' (h.symm '' S) = S := by
    rw [Set.image_image]; simp
  have htightT : IsTightMeasureSet
      {((ν : ProbabilityMeasure Ω) : Measure Ω) | ν ∈ h.symm '' S} := by
    convert htight using 1
    ext m; constructor
    · rintro ⟨ν, ⟨μ, hμ, rfl⟩, rfl⟩; exact ⟨μ, hμ, rfl⟩
    · rintro ⟨μ, hμ, rfl⟩; exact ⟨h.symm μ, ⟨μ, hμ, rfl⟩, rfl⟩
  have hcompactT : IsCompact (closure (h.symm '' S)) :=
    isCompact_closure_of_isTightMeasureSet htightT
  rw [← hST, ← Homeomorph.image_closure]
  exact hcompactT.image h.continuous
/-- On a proper metric space, the Lévy–Prokhorov metric space of probability measures is
complete. -/
instance instCompleteSpaceLevyProkhorovProbabilityMeasure :
    CompleteSpace (LevyProkhorov (ProbabilityMeasure Ω)) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hcompact : IsCompact (closure (Set.range u)) :=
    isCompact_closure_of_isTightMeasureSet_levyProkhorov (Set.range u)
      (_root_.Prove2MeSourceProof.h_c96b33d6be4a8e5dc0e21209 (Set.range u) hu.totallyBounded_range)
  obtain ⟨a, -, φ, hφ, hφlim⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨a, tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop hφlim⟩
end LevyStochCalc.Probability


