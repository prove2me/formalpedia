-- Prove2me | Definitions.Def_SourceProof_f52e0f0d3a3e8c96b04f0727
-- name    : SourceProof_f52e0f0d3a3e8c96b04f0727
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:35.722965+00:00
-- url     : https://prove2.me/theorems/63c82830-e22d-42ea-a904-26cde61fe772
-- title:
--   StochLean source theorem: ProbabilityTheory.ofReal_norm_sub_le_denseWindowOscillation_of_rightContinuous

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowOscillation_F001
import Definitions.Def_SourceProof_1121a4cb53a4defeae5b1f13

open private exists_denseTimeUpTo_right_approximation from Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowOscillation_F001
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable two-time short-window oscillations

The envelope uses two points of the existing clipped dense grid and an actual
order and strict-width guard. Countability makes it measurable. Two right-side
approximating sequences recover every strict window of a right-continuous
path; doubling a positive width also covers a closed-width window. Cadlag
compact boundedness proves finiteness before the real-valued bridge is used.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem _root_.Prove2MeSourceProof.h_f52e0f0d3a3e8c96b04f0727
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsRightContinuousPath (X · ω))
    {T δ r s : ℝ≥0} (hrs : r ≤ s) (hsT : s ≤ T) (hwidth : s < r + δ) :
    ENNReal.ofReal ‖X s ω - X r ω‖ ≤ denseWindowOscillation X T δ ω := by
  rcases hrs.eq_or_lt with he | hrs
  · subst s
    simp only [sub_self, norm_zero, ENNReal.ofReal_zero, zero_le]
  obtain ⟨u, hu⟩ := exists_denseTimeUpTo_right_approximation (hrs.le.trans hsT)
  obtain ⟨v, hv⟩ := exists_denseTimeUpTo_right_approximation hsT
  have hut := hu.mono_right nhdsWithin_le_nhds
  have hvt := hv.mono_right nhdsWithin_le_nhds
  have horder := hut.eventually_lt hvt hrs
  have hwin := hvt.eventually_lt (hut.add tendsto_const_nhds) hwidth
  have hvalue := ((hX s).tendsto.comp hv).sub ((hX r).tendsto.comp hu)
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hvalue.norm
  apply le_of_tendsto hlim
  filter_upwards [horder, hwin] with n hn hw
  exact _root_.Prove2MeSourceProof.h_1121a4cb53a4defeae5b1f13 hn.le hw ω
end ProbabilityTheory


