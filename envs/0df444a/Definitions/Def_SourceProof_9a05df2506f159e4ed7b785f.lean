-- Prove2me | Definitions.Def_SourceProof_9a05df2506f159e4ed7b785f
-- name    : SourceProof_9a05df2506f159e4ed7b785f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:21:34.533547+00:00
-- url     : https://prove2.me/theorems/7a0dc4ad-cf98-54d3-b2b8-d831a10da8e8
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.memLp_sampledProcess_min_const

import Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F002
import Definitions.Def_SourceProof_3ef1b770d86f3f62808f41e0

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

theorem _root_.Prove2MeSourceProof.h_9a05df2506f159e4ed7b785f (π : StoppingTimePartition F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) {p : ℝ≥0∞} (hp : 1 ≤ p) (hXT : MemLp (X T) p P) (n : ℕ) :
    MemLp (π.sampledProcess (fun t ↦ X (min t T)) n) p P :=
  (_root_.Prove2MeSourceProof.h_3ef1b770d86f3f62808f41e0 hX) hF hr (π.pointNat n) T hp hXT
end ProbabilityTheory.StoppingTimePartition


