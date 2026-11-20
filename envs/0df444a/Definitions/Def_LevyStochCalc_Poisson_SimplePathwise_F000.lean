-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimplePathwise_F000
-- name    : LevyStochCalc_Poisson_SimplePathwise_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:50:18.114216+00:00
-- url     : https://prove2.me/theorems/66fc1ac2-ef22-4cf2-8ad2-5b2c1d2e87ea
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimplePathwise
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimplePathwise. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F003
import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F004
import Definitions.Def_LevyStochCalc_Poisson_JumpSum_F000
import Definitions.Def_SourceProof_1fd4456750d7da453c9297b3
import Definitions.Def_SourceProof_c270d540a1c5354737ac7c4b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pathwise form of the elementary compensated integral

A simple predictable integrand is a finite combination of indicators of disjoint time–mark
rectangles, so its integral against any measure finite on those rectangles is the corresponding
finite combination of their masses. The elementary compensated integral at the horizon is
therefore the difference of the integrals against the Poisson random measure and against the
reference intensity, and, over a window where the counts are almost surely atomic, the difference
of a finite jump sum and the compensator.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {T : ℝ}

namespace SimplePredictable

/-- The time–mark rectangles of a simple predictable integrand are measurable. -/
theorem measurableSet_fullRect (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) :
    MeasurableSet (φ.fullRect i) :=
  measurableSet_Ioc.prod (φ.A_measurable i)
/-- The reference intensity of a rectangle is finite. -/
theorem referenceIntensity_fullRect_ne_top (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) :
    LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) ≠ ⊤ := by
  rw [(_root_.Prove2MeSourceProof.h_c270d540a1c5354737ac7c4b φ) i]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (φ.A_finite i)
/-- At the horizon the running rectangle is the full rectangle. -/
theorem timeRect_horizon (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) :
    φ.timeRect i T = φ.fullRect i := by
  have h1 : min (φ.partition i.castSucc) T = φ.partition i.castSucc :=
    min_eq_left ((φ.partition_strictMono.monotone (Fin.le_last _)).trans φ.partition_le_T)
  have h2 : min (φ.partition i.succ) T = φ.partition i.succ :=
    min_eq_left ((φ.partition_strictMono.monotone (Fin.le_last _)).trans φ.partition_le_T)
  rw [SimplePredictable.timeRect, SimplePredictable.fullRect, h1, h2]
/-- The union of the mark sets of a simple predictable integrand. -/
noncomputable def markSet (φ : SimplePredictable Ω E ν T) : Set E := ⋃ i : Fin φ.N, φ.A i
theorem measurableSet_markSet (φ : SimplePredictable Ω E ν T) : MeasurableSet φ.markSet :=
  MeasurableSet.iUnion fun i => φ.A_measurable i
/-- The mark sets have finite total intensity. -/
theorem measure_markSet_ne_top (φ : SimplePredictable Ω E ν T) : ν φ.markSet ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr fun i _ => φ.A_finite i)
    (measure_iUnion_fintype_le ν φ.A)
/-- Every rectangle sits inside the horizon window over the mark sets. -/
theorem fullRect_subset (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) :
    φ.fullRect i ⊆ Set.Ioc (0 : ℝ) T ×ˢ φ.markSet := by
  rintro ⟨t, e⟩ hp
  obtain ⟨ht, he⟩ := Set.mem_prod.mp hp
  obtain ⟨htl, htr⟩ := Set.mem_Ioc.mp ht
  refine Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨?_, ?_⟩, Set.mem_iUnion.mpr ⟨i, he⟩⟩
  · have h0 : φ.partition 0 ≤ φ.partition i.castSucc :=
      φ.partition_strictMono.monotone (Fin.zero_le _)
    rw [φ.partition_zero] at h0
    exact lt_of_le_of_lt h0 htl
  · exact htr.trans ((φ.partition_strictMono.monotone (Fin.le_last _)).trans φ.partition_le_T)
/-- A simple predictable integrand vanishes off the horizon window over its mark sets. -/
theorem eval_eq_zero_of_notMem (φ : SimplePredictable Ω E ν T) (ω : Ω) {p : ℝ × E}
    (hp : p ∉ Set.Ioc (0 : ℝ) T ×ˢ φ.markSet) : φ.eval p.1 p.2 ω = 0 := by
  rw [(_root_.Prove2MeSourceProof.h_1fd4456750d7da453c9297b3 φ) p.1 p.2 ω]
  refine Finset.sum_eq_zero fun i _ => ?_
  refine Set.indicator_of_notMem (fun hmem => hp ?_) _
  exact φ.fullRect_subset i (by simpa using hmem)
/-- The integral of a simple predictable integrand against a measure finite on its rectangles. -/
theorem integral_eval_eq_sum (φ : SimplePredictable Ω E ν T) (μ : Measure (ℝ × E))
    (hfin : ∀ i : Fin φ.N, μ (φ.fullRect i) ≠ ⊤) (ω : Ω) :
    ∫ p, φ.eval p.1 p.2 ω ∂μ = ∑ i : Fin φ.N, (μ (φ.fullRect i)).toReal * φ.ξ i ω := by
  have hrw : (fun p : ℝ × E => φ.eval p.1 p.2 ω)
      = fun p : ℝ × E => ∑ i : Fin φ.N,
        (φ.fullRect i).indicator (fun _ : ℝ × E => φ.ξ i ω) p := by
    funext p
    exact (_root_.Prove2MeSourceProof.h_1fd4456750d7da453c9297b3 φ) p.1 p.2 ω
  rw [hrw, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const _ (φ.measurableSet_fullRect i), smul_eq_mul,
      measureReal_def]
  · intro i _
    rw [integrable_indicator_iff (φ.measurableSet_fullRect i)]
    exact integrableOn_const (hfin i)
end SimplePredictable

section Pathwise

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The elementary compensated integral is pathwise.** At the horizon it is the integral of the
integrand against the Poisson random measure minus its integral against the reference
intensity. -/
theorem simpleIntegral_eq_sub_integral (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (φ : SimplePredictable Ω E ν T) (ω : Ω)
    (hfin : ∀ i : Fin φ.N, N.N ω (φ.fullRect i) ≠ ⊤) :
    simpleIntegral N φ T ω
      = (∫ p, φ.eval p.1 p.2 ω ∂(N.N ω))
        - ∫ p, φ.eval p.1 p.2 ω ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
  rw [φ.integral_eval_eq_sum (N.N ω) hfin ω,
    φ.integral_eval_eq_sum (LevyStochCalc.Poisson.referenceIntensity ν)
      φ.referenceIntensity_fullRect_ne_top ω,
    ← Finset.sum_sub_distrib, simpleIntegral]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated, φ.timeRect_horizon i]
  ring
/-- The counts on the rectangles are almost surely finite. -/
theorem ae_count_fullRect_ne_top (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (φ : SimplePredictable Ω E ν T) :
    ∀ᵐ ω ∂P, ∀ i : Fin φ.N, N.N ω (φ.fullRect i) ≠ ⊤ := by
  refine ae_all_iff.mpr fun i => ?_
  filter_upwards [N.integer_valued (φ.measurableSet_fullRect i)
    (φ.referenceIntensity_fullRect_ne_top i)] with ω hω
  obtain ⟨n, hn⟩ := hω
  rw [hn]
  exact ENNReal.natCast_ne_top n
/-- The pathwise form of the elementary compensated integral, almost surely. -/
theorem ae_simpleIntegral_eq_sub_integral
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (φ : SimplePredictable Ω E ν T) :
    ∀ᵐ ω ∂P, simpleIntegral N φ T ω
      = (∫ p, φ.eval p.1 p.2 ω ∂(N.N ω))
        - ∫ p, φ.eval p.1 p.2 ω ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
  filter_upwards [ae_count_fullRect_ne_top N φ] with ω hω
  exact simpleIntegral_eq_sub_integral N φ ω hω
variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

/-- **The finite-activity identity for elementary integrands.** The elementary compensated
integral at the horizon is almost surely a finite jump sum minus the compensator. -/
theorem ae_exists_finset_simpleIntegral_eq
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (φ : SimplePredictable Ω E ν T) :
    ∀ᵐ ω ∂P, ∃ s : Finset (ℝ × E),
      simpleIntegral N φ T ω
        = (∑ p ∈ s, (((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ φ.markSet)) {p}).toReal
            * φ.eval p.1 p.2 ω)
          - ∫ p, φ.eval p.1 p.2 ω ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
  filter_upwards [ae_simpleIntegral_eq_sub_integral N φ,
    LevyStochCalc.Poisson.ae_exists_finset_integral_eq_sum N
      (measurableSet_Ioc.prod φ.measurableSet_markSet)
      (LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top φ.measure_markSet_ne_top T)]
    with ω hω hsum
  obtain ⟨s, -, hbochner, -⟩ := hsum
  refine ⟨s, ?_⟩
  rw [hω, ← hbochner fun p => φ.eval p.1 p.2 ω,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => φ.eval_eq_zero_of_notMem ω hp]
end Pathwise

end LevyStochCalc.Poisson.Compensated


