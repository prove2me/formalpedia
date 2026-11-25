-- Prove2me | Definitions.Def_SourceProof_7dbceac91c975186454d86e6
-- name    : SourceProof_7dbceac91c975186454d86e6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:26:51.28026+00:00
-- url     : https://prove2.me/theorems/8c863e12-8776-5f36-9f80-349ccdcc9525
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.martingale_sampledProcess_min_const

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F001
import Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F002
import Definitions.Def_SourceProof_01f70dd5a37db7f8f210a188
import Definitions.Def_SourceProof_0bdd61215a21f3b253c38ea5
import Definitions.Def_SourceProof_38b6716030de814054336ad8

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Discrete sampling on a source stopping-time partition

The finite ordered endpoint family is extended constantly after its last index. Its canonical
stopping sigma-fields and sampled process are then indexed by natural numbers, so the existing
discrete martingale and integral owners can be reused without a second finite-index calculus.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

variable [SigmaFiniteFiltration P F]

theorem _root_.Prove2MeSourceProof.h_7dbceac91c975186454d86e6 (π : StoppingTimePartition F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) (T : ℝ≥0) :
    Martingale (π.sampledProcess (fun t ↦ X (min t T))) π.sampledFiltration P :=
  (_root_.Prove2MeSourceProof.h_01f70dd5a37db7f8f210a188 π) ((_root_.Prove2MeSourceProof.h_0bdd61215a21f3b253c38ea5 hX) T).1
    ((_root_.Prove2MeSourceProof.h_0bdd61215a21f3b253c38ea5 hX) T).2 hF (hr.mono (fun _ h ↦ (_root_.Prove2MeSourceProof.h_38b6716030de814054336ad8 h) T))
end ProbabilityTheory.StoppingTimePartition


