-- Prove2me | Definitions.Def_LevyStochCalc_Probability_MarkedPredictableModification_F000
-- name    : LevyStochCalc_Probability_MarkedPredictableModification_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:30:30.391408+00:00
-- url     : https://prove2.me/theorems/6a7d480c-1982-4d8a-8d64-b23b9a4792ec
-- title:
--   Source declarations: LevyStochCalc.Probability.MarkedPredictableModification
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.MarkedPredictableModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F003
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictable_F001
import Definitions.Def_SourceProof_fdeeab164202d120da06e07d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Predictable representatives of marked progressive integrands

A mark-step integrand adapted at the left endpoints of its cells is predictable on the time–mark
space, and the marked predictable processes are closed under pointwise upper limits. The
mark-step integrands are dense in the marked progressive integrands of finite energy, so such an
integrand agrees with a predictable one almost everywhere in time, mark and sample point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {ℱ : Filtration ℝ mΩ}

open LevyStochCalc.Poisson.Compensated

/-- **An adapted mark-step integrand is predictable.** -/
theorem markedPredictable_markStepEval {g : TimeGrid} (G : MarkStep Ω E ν g)
    (hG : G.Adapted ℱ) : MarkedPredictable ℱ ν fun ω s e => G.eval s e ω := by
  have hrw : (fun p : Ω × ℝ × E => G.eval p.2.1 p.2.2 p.1)
      = fun p : Ω × ℝ × E => ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
        (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k p.1) (p.2.1, p.2.2) := by
    funext p
    rw [MarkStep.eval]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hs : p.2.1 ∈ Set.Ioc (g.p i) (g.p (i + 1))
    · rw [Set.indicator_of_mem hs, one_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases he : p.2.2 ∈ G.B k
      · rw [Set.indicator_of_mem he, Set.indicator_of_mem (Set.mk_mem_prod hs he), mul_one]
      · rw [Set.indicator_of_notMem he,
          Set.indicator_of_notMem (fun hp => he hp.2), mul_zero]
    · rw [Set.indicator_of_notMem hs, zero_mul]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      exact Set.indicator_of_notMem (fun hp => hs hp.1) _
  change Measurable[markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E => G.eval p.2.1 p.2.2 p.1
  rw [hrw]
  refine Finset.measurable_sum _ fun i hi => Finset.measurable_sum _ fun k _ => ?_
  exact _root_.Prove2MeSourceProof.h_fdeeab164202d120da06e07d (g.p_nonneg (Finset.mem_range.mp hi).le)
    (G.B_measurable k) (G.B_finite k) (hG i (Finset.mem_range.mp hi) k).measurable
omit [SigmaFinite ν] in
/-- **Marked predictable processes are closed under pointwise upper limits.** -/
theorem MarkedPredictable.limsup {ψ : ℕ → Ω → ℝ → E → ℝ}
    (h : ∀ n, MarkedPredictable ℱ ν (ψ n)) :
    MarkedPredictable ℱ ν fun ω s e => Filter.limsup (fun n => ψ n ω s e) atTop :=
  Measurable.limsup fun n => h n
/-- The pointwise upper limit along a subsequence of mark-step integrands. -/
noncomputable def limsupMarkStepEval {g : ℕ → TimeGrid} (G : ∀ n, MarkStep Ω E ν (g n))
    (ns : ℕ → ℕ) : Ω → ℝ → E → ℝ :=
  fun ω s e => limsup (fun i => (G (ns i)).eval s e ω) atTop
variable {P : Measure Ω} [IsProbabilityMeasure P]

end LevyStochCalc.Probability


