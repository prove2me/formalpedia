-- Prove2me | Definitions.Def_SourceProof_4cb05f474a070d71055c9fca
-- name    : SourceProof_4cb05f474a070d71055c9fca
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:51:41.723448+00:00
-- url     : https://prove2.me/theorems/61661f49-5c16-4a8f-8f9d-c8eec9117a97
-- title:
--   StochLean source theorem: ProbabilityTheory.HasCadlagPaths.largeJumpSumProcesses_properties

import Definitions.Def_StochLean_Probability_Process_Path_LargeJumpSum_F000
import Definitions.Def_SourceProof_545f2f59d5d65e5b39471fc0
import Definitions.Def_SourceProof_72a1ab211be956ee5d818cd1
import Definitions.Def_SourceProof_8721f78b0017a7455a9a15ba
import Definitions.Def_SourceProof_bb9318db62d4de7b533abf62
import Definitions.Def_SourceProof_de298d81ae177af385de3ac2

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The actual large-jump cumulative processes

These are the signed and norm sums of the original jumps strictly larger
than the threshold, over the actual positive-time interval. They do not
select a decomposition or depend on an enumeration. The deterministic
locally finite sum results give common-event cadlag/FV properties and the
exact jumps. Measurability and locally integrable variation are separate
later conclusions, not part of the definitions.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*}

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} {b : ℝ}

namespace HasCadlagPaths

theorem _root_.Prove2MeSourceProof.h_4cb05f474a070d71055c9fca (hc : HasCadlagPaths X P)
    (hb : 0 < b) :
    HasCadlagPaths (largeJumpSumProcess X b) P ∧
      HasCadlagPaths (largeJumpNormSumProcess X b) P ∧
      HasFiniteVariationPaths (largeJumpSumProcess X b) P ∧
      HasMonotonePaths (largeJumpNormSumProcess X b) P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ largeJumpNormSumProcess X b t ω) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        eVariationOn (largeJumpSumProcess X b · ω) (Icc 0 T) ≤
          ENNReal.ofReal (largeJumpNormSumProcess X b T ω)) := by
  have hm : ProbabilityTheory.HasMonotonePaths (ProbabilityTheory.largeJumpNormSumProcess X b) P :=
    hc.mono fun _ hω ↦ (_root_.Prove2MeSourceProof.h_de298d81ae177af385de3ac2 hω) hb
  refine ⟨hc.mono (fun _ hω ↦ ((_root_.Prove2MeSourceProof.h_72a1ab211be956ee5d818cd1 hω) hb).1),
    hc.mono (fun _ hω ↦ ((_root_.Prove2MeSourceProof.h_72a1ab211be956ee5d818cd1 hω) hb).2),
    hc.mono (fun _ hω ↦ (_root_.Prove2MeSourceProof.h_545f2f59d5d65e5b39471fc0 hω) hb),
    hm, ?_, hc.mono (fun _ hω ↦ (_root_.Prove2MeSourceProof.h_bb9318db62d4de7b533abf62 hω) hb)⟩
  filter_upwards [hm] with ω hω t
  have h := hω (bot_le : (0 : ℝ≥0) ≤ t)
  change ProbabilityTheory.largeJumpNormSumProcess X b 0 ω ≤ ProbabilityTheory.largeJumpNormSumProcess X b t ω at h
  simpa only [(_root_.Prove2MeSourceProof.h_8721f78b0017a7455a9a15ba X b).2, Pi.zero_apply] using h
end HasCadlagPaths

end ProbabilityTheory


