-- Prove2me | Definitions.Def_SourceProof_2e0d0236117e214012bd8888
-- name    : SourceProof_2e0d0236117e214012bd8888
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:27:10.078306+00:00
-- url     : https://prove2.me/theorems/8827626f-02f0-5a38-9473-81fa5d6203e6
-- title:
--   StochLean source theorem: ProbabilityTheory.CagladApproximation.toProcess_eq_zero_of_zero_path

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_OscillationApproximation_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Oscillation approximants preserve zero sample paths

This is a pointwise property of the actual construction. It does not require
the zero-path event to be measurable in the initial sigma-algebra.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.CagladApproximation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_2e0d0236117e214012bd8888 (H : ℝ≥0 → Ω → ℝ) (ha : Adapted F H)
    (hF : F.IsUsual P) (hc : HasCagladPaths H P) (ε : ℝ) (hε : 0 ≤ ε)
    (n : ℕ) (T : ℝ≥0) {ω : Ω} (hzero : ∀ t, H t ω = 0) (t : ℝ≥0) :
    (representation H ha hF hc ε hε n T).toProcess t ω = 0 := by
  have hrl (s : ℝ≥0) : ProbabilityTheory.rightLimitProcess H s ω = 0 := by
    change Function.rightLim (fun u ↦ H u ω) s = 0
    rw [show (fun u ↦ H u ω) = fun _ ↦ (0 : ℝ) from funext hzero]
    exact continuousWithinAt_const.rightLim_eq
  simp only [ProbabilityTheory.SimplePredictableRep.toProcess, ProbabilityTheory.CagladApproximation.representation, hzero, hrl,
    ite_self, Finset.sum_const_zero]
end ProbabilityTheory.CagladApproximation


