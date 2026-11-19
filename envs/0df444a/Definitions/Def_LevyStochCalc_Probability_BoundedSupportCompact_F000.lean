-- Prove2me | Definitions.Def_LevyStochCalc_Probability_BoundedSupportCompact_F000
-- name    : LevyStochCalc_Probability_BoundedSupportCompact_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:00:44.54191+00:00
-- url     : https://prove2.me/theorems/28bd7b80-beb2-437d-8523-9ad944132c78
-- title:
--   Source declarations: LevyStochCalc.Probability.BoundedSupportCompact
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.BoundedSupportCompact. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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
# Probability measures concentrated on a compact set

For a compact set `K`, the probability measures that give no mass to `Kᶜ` form a compact set for
the topology of convergence in distribution: the set is tight, since every member puts full mass
on `K`, and closed, since `μ ↦ μ Kᶜ` is lower semicontinuous by the portmanteau theorem; Prokhorov's
theorem then gives compactness. On a separable metric space the same set, viewed in the
Lévy–Prokhorov metric, is therefore a complete metric space.

## Main statements

* `LevyStochCalc.Probability.isCompact_setOf_measure_compl_eq_zero` — compactness in the topology
  of convergence in distribution.
* `LevyStochCalc.Probability.completeSpace_levyProkhorov_measure_compl_eq_zero` — completeness in
  the Lévy–Prokhorov metric.
-/

open MeasureTheory Filter Set Topology TopologicalSpace

namespace LevyStochCalc.Probability

/-- For a compact set `K`, the probability measures giving no mass to `Kᶜ` form a compact set in
the topology of convergence in distribution. -/
theorem isCompact_setOf_measure_compl_eq_zero {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [T2Space E] [BorelSpace E] [HasOuterApproxClosed E] {K : Set E} (hK : IsCompact K) :
    IsCompact {μ : ProbabilityMeasure E | (μ : Measure E) Kᶜ = 0} := by
  set T := {μ : ProbabilityMeasure E | (μ : Measure E) Kᶜ = 0} with hT
  have htight : IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ T} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    refine fun ε _ => ⟨K, hK, ?_⟩
    rintro _ ⟨ν, hν, rfl⟩
    rw [hT, mem_setOf_eq] at hν
    rw [hν]
    exact zero_le
  have hclosed : IsClosed T := by
    refine isClosed_of_closure_subset fun μ hμ => ?_
    haveI : (𝓝[T] μ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hμ
    have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto id (𝓝[T] μ) (𝓝 μ))
      hK.isClosed.isOpen_compl
    have hev : (fun ν : ProbabilityMeasure E => ((id ν : ProbabilityMeasure E) : Measure E) Kᶜ)
        =ᶠ[𝓝[T] μ] fun _ => 0 :=
      eventually_nhdsWithin_of_forall fun ν hν => hν
    rw [liminf_congr hev, liminf_const] at hle
    exact nonpos_iff_eq_zero.mp hle
  simpa [hclosed.closure_eq] using isCompact_closure_of_isTightMeasureSet htight
/-- On a separable metric space, for a compact set `K`, the probability measures giving no mass to
`Kᶜ` form a complete subspace of the Lévy–Prokhorov metric space. -/
theorem completeSpace_levyProkhorov_measure_compl_eq_zero {E : Type*} [MetricSpace E]
    [SeparableSpace E] [MeasurableSpace E] [BorelSpace E] {K : Set E} (hK : IsCompact K) :
    CompleteSpace {μ : LevyProkhorov (ProbabilityMeasure E) //
      (LevyProkhorov.toMeasure μ).toMeasure Kᶜ = 0} := by
  have hcompact : IsCompact {μ : LevyProkhorov (ProbabilityMeasure E) |
      (LevyProkhorov.toMeasure μ).toMeasure Kᶜ = 0} := by
    have h := (isCompact_setOf_measure_compl_eq_zero hK).image
      (LevyProkhorov.probabilityMeasureHomeomorph (Ω := E)).continuous
    rw [Homeomorph.image_eq_preimage_symm] at h
    exact h
  exact hcompact.isComplete.completeSpace_coe
end LevyStochCalc.Probability


