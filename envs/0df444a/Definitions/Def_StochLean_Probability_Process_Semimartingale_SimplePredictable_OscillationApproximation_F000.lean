-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_OscillationApproximation_F000
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_OscillationApproximation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:24:25.738802+00:00
-- url     : https://prove2.me/theorems/846b2b0f-77f9-4d1f-b0fa-b64e7f41d91f
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable.OscillationApproximation F000

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Partition_TruncateSequence_F000
import Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Oscillation_F002
import Definitions.Def_SourceProof_1a34da0744a1e367373a463f
import Definitions.Def_SourceProof_4aad6e35fadea08fff8ce9d0
import Definitions.Def_SourceProof_53bca36d7403deaa0689f5ec
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_d4e3aa776085075e566a42af
import Definitions.Def_SourceProof_e8ced37b953a339f0596f831
import Definitions.Def_SourceProof_f60f6796fd78b83be1f764d1
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual finite simple approximants from oscillation partitions

The first interval is included. The source initial value is sampled independently;
positive-time coefficients sample the right-limit process at finite capped left
endpoints, never at infinity. Bounds hold on the original common caglad path event.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.CagladApproximation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  (H : ℝ≥0 → Ω → ℝ) (ha : Adapted F H) (hF : F.IsUsual P) (hc : HasCagladPaths H P)

noncomputable def partition (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (T : ℝ≥0) :
    StoppingTimePartition F :=
  StoppingTimePartition.truncateSequence (oscillationTimes (rightLimitProcess H) ε)
    (_root_.Prove2MeSourceProof.h_1a34da0744a1e367373a463f ((_root_.Prove2MeSourceProof.h_f60f6796fd78b83be1f764d1 ha) hF hc) hF
      (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c (_root_.Prove2MeSourceProof.h_53bca36d7403deaa0689f5ec hc)) ε)
    (_root_.Prove2MeSourceProof.h_d4e3aa776085075e566a42af hε) (_root_.Prove2MeSourceProof.h_e8ced37b953a339f0596f831 ε) n T
noncomputable def representation (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (T : ℝ≥0) :
    SimplePredictableRep F where
  partition := partition H ha hF hc ε hε n T
  initial := H 0
  measurable_initial := ha 0
  coefficient := fun i ω ↦ rightLimitProcess H
    ((partition H ha hF hc ε hε n T).point i.castSucc ω) ω
  measurable_coefficient := fun i ↦
    (_root_.Prove2MeSourceProof.h_4aad6e35fadea08fff8ce9d0 ((_root_.Prove2MeSourceProof.h_f60f6796fd78b83be1f764d1 ha) hF hc).stronglyAdapted) hF
      (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c (_root_.Prove2MeSourceProof.h_53bca36d7403deaa0689f5ec hc))
      ((partition H ha hF hc ε hε n T).point i.castSucc).isStoppingTime
end ProbabilityTheory.CagladApproximation


