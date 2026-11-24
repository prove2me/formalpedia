-- Prove2me | Definitions.Def_SourceProof_5ca4405816bfb3226bfbfb78
-- name    : SourceProof_5ca4405816bfb3226bfbfb78
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:39.634888+00:00
-- url     : https://prove2.me/theorems/41f96609-7cd0-407b-8038-533e9c50548d
-- title:
--   StochLean source theorem: ProbabilityTheory.isGoodIntegrator_of_elementaryIntegral_l2_estimate

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_20a93e82df5614593d650dd1
import Definitions.Def_SourceProof_91776c6d66e3ec9a393c48f3
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Square-integrable martingales are source semimartingales

The good-integrator property is proved from the elementary L2 estimate and Markov's
inequality, not assumed as part of a martingale definition or inferred from a decomposition.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_5ca4405816bfb3226bfbfb78 (K : ℝ)
    (hbound : ∀ C : ℝ≥0, ∀ H : ℝ≥0 → Ω → ℝ, ∀ hH : IsSimplePredictable H F,
      (∀ t ω, ‖H t ω‖ ≤ C) →
        Integrable (fun ω ↦ (hH.elementaryIntegral X ω) ^ 2) P ∧
          (∫ ω, (hH.elementaryIntegral X ω) ^ 2 ∂P) ≤ (C : ℝ) ^ 2 * K) :
    IsGoodIntegrator X F P := by
  apply _root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3.mpr
  intro ε hε η hη
  have hlim : Tendsto (fun n : ℕ ↦
      ENNReal.ofReal ((1 / ((n : ℝ) + 1)) ^ 2 * K / ε ^ 2)) atTop (𝓝 0) := by
    have hr := ((tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).mul_const K).div_const (ε ^ 2)
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_div,
      ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hη).exists
  let C : ℝ≥0 := ⟨1 / ((n : ℝ) + 1), by positivity⟩
  refine ⟨(C : ℝ), (show 0 < (1 / ((n : ℝ) + 1)) from one_div_pos.mpr (by positivity)),
    fun H hH hb ↦ ?_⟩
  obtain ⟨hi, he⟩ := hbound C H hH hb
  calc
    _ ≤ ENNReal.ofReal ((∫ ω, (hH.elementaryIntegral X ω) ^ 2 ∂P) / ε ^ 2) :=
      _root_.Prove2MeSourceProof.h_20a93e82df5614593d650dd1 hi hε
    _ ≤ ENNReal.ofReal ((C : ℝ) ^ 2 * K / ε ^ 2) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right he (sq_nonneg _))
    _ ≤ η := hn.le
variable [SigmaFiniteFiltration P F]

end ProbabilityTheory


