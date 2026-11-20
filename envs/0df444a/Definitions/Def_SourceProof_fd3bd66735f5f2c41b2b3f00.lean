-- Prove2me | Definitions.Def_SourceProof_fd3bd66735f5f2c41b2b3f00
-- name    : SourceProof_fd3bd66735f5f2c41b2b3f00
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:37:15.714715+00:00
-- url     : https://prove2.me/theorems/d5aa460c-ee31-4eff-a76d-287c7ea403d4
-- title:
--   LevyStochCalc source module: SourceProof_fd3bd66735f5f2c41b2b3f00
-- statement:
--   The original source theorem `LevyStochCalc.Probability.markedPredictable_of_continuous_adapted` comes from the `LevyStochCalc.Probability.PredictableContinuous` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_PredictableContinuous_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A continuous adapted process, cut to a window, is marked predictable

Freezing a continuous adapted process at the left endpoints of the level-`n` dyadic slabs gives a
step process whose coefficients are known at those endpoints, hence a marked predictable process
for every level. The endpoints increase to the time from strictly below, so on a window of finite
mark measure the frozen processes converge pointwise to the process itself, which is therefore
marked predictable there.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

open LevyStochCalc.Poisson (dyadicLeft dyadicLeft_lt sub_le_dyadicLeft)


theorem _root_.Prove2MeSourceProof.h_fd3bd66735f5f2c41b2b3f00 {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hX : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t))
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    MarkedPredictable ℱ ν fun ω s e =>
      (Set.Ioc (0 : ℝ) T ×ˢ A).indicator (fun _ : ℝ × E => X s ω) (s, e) := by
  have hstep : ∀ n : ℕ, Measurable[LevyStochCalc.Probability.markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
      LevyStochCalc.Probability.stepEvalCut X A T n p.1 p.2.1 p.2.2 := fun n =>
    LevyStochCalc.Probability.markedPredictable_stepEvalCut hX hA hAν T n
  change Measurable[LevyStochCalc.Probability.markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
    (Set.Ioc (0 : ℝ) T ×ˢ A).indicator (fun _ : ℝ × E => X p.2.1 p.1) (p.2.1, p.2.2)
  refine @measurable_of_tendsto_metrizable' _ _ (LevyStochCalc.Probability.markedPredictableSigma ℱ ν) _ _ _ _ ℕ
    (fun n p => LevyStochCalc.Probability.stepEvalCut X A T n p.1 p.2.1 p.2.2) _ atTop _ _ hstep ?_
  refine tendsto_pi_nhds.mpr fun p => ?_
  by_cases hp : (p.2.1, p.2.2) ∈ Set.Ioc (0 : ℝ) T ×ˢ A
  · obtain ⟨⟨hs0, hsT⟩, he⟩ := hp
    have hmem : (p.2.1, p.2.2) ∈ Set.Ioc (0 : ℝ) T ×ˢ A := ⟨⟨hs0, hsT⟩, he⟩
    rw [Set.indicator_of_mem hmem]
    have heq : ∀ n : ℕ, LevyStochCalc.Probability.stepEvalCut X A T n p.1 p.2.1 p.2.2 = X (LevyStochCalc.Poisson.dyadicLeft n p.2.1) p.1 := by
      intro n
      rw [LevyStochCalc.Probability.stepEvalCut, Set.indicator_of_mem hmem, one_mul, LevyStochCalc.Probability.stepEval_eq hs0 hsT he p.1 n]
    simp only [heq]
    refine ((hXc p.1).tendsto (p.2.1)).comp ?_
    have hlo : ∀ n : ℕ, p.2.1 - (1 / 2 : ℝ) ^ n ≤ LevyStochCalc.Poisson.dyadicLeft n p.2.1 := fun n =>
      LevyStochCalc.Poisson.sub_le_dyadicLeft n
    have hhi : ∀ n : ℕ, LevyStochCalc.Poisson.dyadicLeft n p.2.1 ≤ p.2.1 := fun n => (LevyStochCalc.Poisson.dyadicLeft_lt hs0 n).le
    have hlim : Tendsto (fun n : ℕ => p.2.1 - (1 / 2 : ℝ) ^ n) atTop (𝓝 p.2.1) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)
      simpa using (tendsto_const_nhds (x := p.2.1)).sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlo hhi
  · rw [Set.indicator_of_notMem hp]
    have hzero : ∀ n : ℕ, LevyStochCalc.Probability.stepEvalCut X A T n p.1 p.2.1 p.2.2 = 0 := by
      intro n
      rw [LevyStochCalc.Probability.stepEvalCut, Set.indicator_of_notMem hp, zero_mul]
    simp only [hzero]
    exact tendsto_const_nhds
end LevyStochCalc.Probability


