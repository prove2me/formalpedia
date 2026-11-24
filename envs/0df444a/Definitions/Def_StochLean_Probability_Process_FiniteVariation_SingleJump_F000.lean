-- Prove2me | Definitions.Def_StochLean_Probability_Process_FiniteVariation_SingleJump_F000
-- name    : StochLean_Probability_Process_FiniteVariation_SingleJump_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:04.205185+00:00
-- url     : https://prove2.me/theorems/1dbab49d-7e07-4a59-99b3-c5d37c8ec754
-- title:
--   StochLean: Probability.Process.FiniteVariation.SingleJump F000

import Definitions.Def_StochLean_Analysis_PathVariation_CompletedSums_F001
import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Integrable_F000
import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Integrable_F001
import Definitions.Def_SourceProof_59980e478d16e5d17042fad7
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual integrable variation of a single lifetime step

The closed-step process uses the existing lifetime indicator. Its whole-half-line
extended variation is exactly the norm of its coefficient at a positive finite
lifetime, and zero at zero or infinite lifetime. A zero lifetime gives a constant
path, so its initial value contributes no variation. An infinite lifetime never
activates at a finite time.

The variation formula is pathwise and needs no measurability. A measurable
lifetime and an integrable coefficient then give actual integrable variation
and its expectation bound. Neither a filtration, a stopping-time hypothesis,
finiteness of the measure, nor a zero initial value is required. Finiteness of
the extended variation is proved before using its real conversion.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

private theorem eVariationOn_step_Ici_univ (a : ℝ≥0) (c : ℝ) :
    eVariationOn (fun t : ℝ≥0 ↦ if a ≤ t then c else 0) univ =
      if 0 < a then ENNReal.ofReal ‖c‖ else 0 := by
  classical
  by_cases ha : 0 < a
  · rw [if_pos ha]
    apply le_antisymm
    · have he : StochLean.cumulativeStepSum (fun _ : Unit ↦ a) (fun _ ↦ c) =
          (fun t : ℝ≥0 ↦ if a ≤ t then c else 0) := by
        funext t
        simp only [StochLean.cumulativeStepSum, Fintype.sum_unique]
      have hb := _root_.Prove2MeSourceProof.h_59980e478d16e5d17042fad7 (fun _ : Unit ↦ a)
        (fun _ : Unit ↦ c) univ
      rw [he] at hb
      simpa only [Fintype.sum_unique, Real.norm_eq_abs] using hb
    · have h := eVariationOn.edist_le (fun t : ℝ≥0 ↦ if a ≤ t then c else 0)
        (mem_univ a) (mem_univ 0)
      simpa only [le_refl, if_true, not_le.mpr ha, if_false, edist_dist,
        dist_zero_right] using h
  · rw [if_neg ha]
    have hz : a = 0 := le_antisymm (le_of_not_gt ha) bot_le
    subst a
    apply (eVariationOn.eq_zero_iff _).mpr
    intro s _ t _
    simp only [zero_le, if_true, edist_self]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ}

end ProbabilityTheory


