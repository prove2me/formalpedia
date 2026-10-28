-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Time_DenseTimeApproximationFromAbove
-- name    : MarkovProcessModule_MarkovProcess_Time_DenseTimeApproximationFromAbove
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:41:03.543362+00:00
-- url     : https://prove2.me/theorems/d927fb7a-1ca2-4075-8749-a8c13ee9cb2a
-- title:
--   MarkovProcess.Time.DenseTimeApproximationFromAbove
-- statement:
--   # Dense-time approximation from above
--
--   Every nonnegative real time is the limit of a strictly decreasing sequence of dense times whose
--   physical values stay strictly above the limit. This includes time zero and times that already
--   belong to the dense carrier; choosing strict upper approximants gives one uniform API for all
--   cuts.
--
--   This is deterministic order-topological infrastructure and makes no stochastic-process claim.
--
--   Complete pinned Lean module MarkovProcess.Time.DenseTimeApproximationFromAbove by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Time/DenseTimeApproximationFromAbove.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Continuity_DenseTimeContinuousExtension

/-!
# Dense-time approximation from above

Every nonnegative real time is the limit of a strictly decreasing sequence of dense times whose
physical values stay strictly above the limit. This includes time zero and times that already
belong to the dense carrier; choosing strict upper approximants gives one uniform API for all
cuts.

This is deterministic order-topological infrastructure and makes no stochastic-process claim.
-/

open Filter Topology
open scoped NNReal

namespace MarkovProcess

/-- Every nonnegative real time admits strictly decreasing dense-time approximants whose physical
values remain strictly above it. -/
theorem exists_denseTime_seq_strictAnti_tendsto (s : NNReal) :
    ∃ q : ℕ → DenseTime,
      StrictAnti q ∧
        (∀ n, s < DenseTime.castOrderEmbedding (q n)) ∧
          Tendsto (fun n ↦ DenseTime.castOrderEmbedding (q n)) atTop (nhds s) := by
  obtain ⟨q, hqAnti, hqAbove, hq⟩ :=
    ContinuousPath.denseRange_castOrderEmbedding.exists_seq_strictAnti_tendsto
      DenseTime.castOrderEmbedding.monotone s
  exact ⟨q, hqAnti, fun n ↦ hqAbove n, by
    simpa only [Function.comp_apply] using! hq⟩

end MarkovProcess


