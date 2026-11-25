-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowMoments_F001
-- name    : StochLean_Probability_Process_Path_CadlagWindowMoments_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:02:16.032791+00:00
-- url     : https://prove2.me/theorems/5183ca72-2eeb-4b9c-86b2-7138a96f9b43
-- title:
--   StochLean: Probability.Process.Path.CadlagWindowMoments F001

import Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowOscillation_F000
import Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowOscillation_F001
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Fixed-cap second moments of short cadlag windows

On a measurable good event with jumps bounded by `b`, the positive excess of
the squared capped window envelope over `b²` tends to zero. A fixed cap gives
integrable domination without any moment assumption on a jump count. The
result bounds the asymptotic second moment, but does not presume convergence
of the envelope itself or control a cap that varies with the width.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

private theorem tendsto_sq_excess_of_eventually_le {ι : Type*} {l : Filter ι}
    {d : ι → ℝ} {b : ℝ} (hb : 0 ≤ b) (hd : ∀ i, 0 ≤ d i)
    (hbound : ∀ η : ℝ, 0 < η → ∀ᶠ i in l, d i ≤ b + η) :
    Tendsto (fun i ↦ max ((d i) ^ 2 - b ^ 2) 0) l (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun i ↦ ha.trans_le (le_max_right _ _)
  · intro a ha
    let η : ℝ := min 1 (a / (4 * (b + 1)))
    have hden : 0 < 4 * (b + 1) := by positivity
    have hη : 0 < η := lt_min zero_lt_one (div_pos ha hden)
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηa : η * (4 * (b + 1)) ≤ a :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    filter_upwards [hbound η hη] with i hi
    have hs : (d i) ^ 2 ≤ (b + η) ^ 2 :=
      (sq_le_sq₀ (hd i) (add_nonneg hb hη.le)).mpr hi
    have hηsq : η ^ 2 ≤ η := by
      simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hη1 hη.le
    have hsmall : (d i) ^ 2 - b ^ 2 < a := by
      nlinarith only [hs, hηsq, hηa, ha, hb, hη.le]
    exact max_lt hsmall ha
end ProbabilityTheory


