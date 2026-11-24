-- Prove2me | Definitions.Def_SourceProof_91776c6d66e3ec9a393c48f3
-- name    : SourceProof_91776c6d66e3ec9a393c48f3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:15.249052+00:00
-- url     : https://prove2.me/theorems/b61ef466-d5f0-4b28-bb57-0505d1f10a1f
-- title:
--   StochLean source theorem: ProbabilityTheory.isGoodIntegrator_iff_continuousAtZero

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Semimartingales as good integrators

The canonical predicate is zero-sequential continuity of the elementary
integral for uniform convergence in `(t,ω)`. The epsilon/delta source
continuity criterion is proved equivalent. Classical decompositions are not
part of this definition. This file does not select a stochastic integral for
general caglad integrands or a quadratic variation.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}


theorem _root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3 :
    IsGoodIntegrator X F P ↔ ElementaryIntegralContinuousAtZero X F P := by
  classical
  constructor
  · intro hX ε hε η hη
    by_contra h
    push Not at h
    have hchoice : ∀ n : ℕ, ∃ H : ℝ≥0 → Ω → ℝ, ∃ hH : ProbabilityTheory.IsSimplePredictable H F,
        (∀ t ω, ‖H t ω‖ ≤ 1 / ((n : ℝ) + 1)) ∧
          η < P {ω | ε ≤ ‖hH.elementaryIntegral X ω‖} := by
      intro n
      exact h (1 / ((n : ℝ) + 1)) (by positivity)
    choose H hH hb hm using hchoice
    have hu : TendstoUniformly (fun n (z : ℝ≥0 × Ω) ↦ H n z.1 z.2)
        (fun _ ↦ 0) atTop := by
      apply Metric.tendstoUniformly_iff.mpr
      intro δ hδ
      have hlim : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      filter_upwards [hlim.eventually_lt_const hδ] with n hn
      intro z
      simpa only [dist_zero_left] using (hb n z.1 z.2).trans_lt hn
    have hlim := (tendstoInMeasure_iff_norm.mp (hX H hH hu)) ε hε
    simp only [Pi.zero_apply, sub_zero] at hlim
    have hle : η ≤ 0 := ge_of_tendsto' hlim fun n ↦ (hm n).le
    exact (not_le_of_gt hη) hle
  · intro hX H hH hu
    apply tendstoInMeasure_iff_norm.mpr
    intro ε hε
    simp only [Pi.zero_apply, sub_zero]
    apply ENNReal.tendsto_atTop_zero.mpr
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hX ε hε η hη
    obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hu δ hδ)
    refine ⟨N, fun n hn ↦ hbound (H n) (hH n) ?_⟩
    intro t ω
    have h := hN n hn (t, ω)
    simpa only [dist_zero_left] using h.le
end ProbabilityTheory


