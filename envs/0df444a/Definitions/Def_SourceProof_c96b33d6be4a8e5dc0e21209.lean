-- Prove2me | Definitions.Def_SourceProof_c96b33d6be4a8e5dc0e21209
-- name    : SourceProof_c96b33d6be4a8e5dc0e21209
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T16:59:00.991981+00:00
-- url     : https://prove2.me/theorems/2cc7ace0-0c6a-4878-8807-ec29fee7765a
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.isTightMeasureSet_of_totallyBounded
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

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


theorem _root_.Prove2MeSourceProof.h_c96b33d6be4a8e5dc0e21209
    (S : Set (LevyProkhorov (ProbabilityMeasure Ω))) (hS : TotallyBounded S) :
    IsTightMeasureSet {(μ.toMeasure.toMeasure : Measure Ω) | μ ∈ S} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with hε_top | hε_ne
  · exact ⟨∅, isCompact_empty, fun μ _ => hε_top ▸ le_top⟩
  have half_pos : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have tight_pt : ∀ y : LevyProkhorov (ProbabilityMeasure Ω),
      ∃ K : Set Ω, IsCompact K ∧ (y.toMeasure.toMeasure) Kᶜ ≤ ε / 2 := by
    intro y
    obtain ⟨K, hK, hKb⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_singleton (μ := y.toMeasure.toMeasure))) (ε / 2) half_pos
    exact ⟨K, hK, hKb _ rfl⟩
  choose Kf hKf_compact hKf_bound using tight_pt
  rw [EMetric.totallyBounded_iff] at hS
  obtain ⟨F, hF_fin, hF_cover⟩ := hS (ε / 2) half_pos
  refine ⟨⋃ y ∈ F, Metric.cthickening (ε / 2).toReal (Kf y),
    hF_fin.isCompact_biUnion (fun y _ => (hKf_compact y).cthickening), ?_⟩
  rintro m ⟨μ, hμS, rfl⟩
  obtain ⟨y, hyF, hμy⟩ := Set.mem_iUnion₂.mp (hF_cover hμS)
  rw [Metric.mem_eball] at hμy
  have hlp : levyProkhorovEDist μ.toMeasure.toMeasure y.toMeasure.toMeasure < ε / 2 := by
    rw [← LevyProkhorov.edist_probabilityMeasure_def]; exact hμy
  set Ky' := Metric.cthickening (ε / 2).toReal (Kf y) with hKy'
  have hKy'_meas : MeasurableSet Ky' := Metric.isClosed_cthickening.measurableSet
  have hKf_meas : MeasurableSet (Kf y) := (hKf_compact y).isClosed.measurableSet
  have hstar : y.toMeasure.toMeasure (Kf y) ≤ μ.toMeasure.toMeasure Ky' + ε / 2 := by
    calc y.toMeasure.toMeasure (Kf y)
        ≤ μ.toMeasure.toMeasure (Metric.thickening (ε / 2).toReal (Kf y)) + ε / 2 :=
          right_measure_le_of_levyProkhorovEDist_lt hlp hKf_meas
      _ ≤ μ.toMeasure.toMeasure Ky' + ε / 2 := by
          rw [hKy']
          gcongr
          exact Metric.thickening_subset_cthickening _ _
  have hμ_total : μ.toMeasure.toMeasure Ky' + μ.toMeasure.toMeasure Ky'ᶜ = 1 := by
    rw [measure_add_measure_compl hKy'_meas]; exact measure_univ
  have hy_total : y.toMeasure.toMeasure (Kf y) + y.toMeasure.toMeasure (Kf y)ᶜ = 1 := by
    rw [measure_add_measure_compl hKf_meas]; exact measure_univ
  have hkey : μ.toMeasure.toMeasure Ky' + μ.toMeasure.toMeasure Ky'ᶜ
      ≤ μ.toMeasure.toMeasure Ky' + (ε / 2 + ε / 2) := by
    calc μ.toMeasure.toMeasure Ky' + μ.toMeasure.toMeasure Ky'ᶜ
        = 1 := hμ_total
      _ = y.toMeasure.toMeasure (Kf y) + y.toMeasure.toMeasure (Kf y)ᶜ := hy_total.symm
      _ ≤ (μ.toMeasure.toMeasure Ky' + ε / 2) + ε / 2 := add_le_add hstar (hKf_bound y)
      _ = μ.toMeasure.toMeasure Ky' + (ε / 2 + ε / 2) := by rw [add_assoc]
  have hbound : μ.toMeasure.toMeasure Ky'ᶜ ≤ ε / 2 + ε / 2 :=
    (ENNReal.add_le_add_iff_left (measure_ne_top _ _)).mp hkey
  rw [ENNReal.add_halves] at hbound
  refine le_trans (measure_mono ?_) hbound
  rw [hKy']
  exact Set.compl_subset_compl.mpr
    (Set.subset_biUnion_of_mem (u := fun y => Metric.cthickening (ε / 2).toReal (Kf y)) hyF)
end LevyStochCalc.Probability


