-- Prove2me | Definitions.Def_MarkovProcess_V3H_Time_DenseTimeApproximationFromAbove_7f339f12
-- name    : MarkovProcess_V3H_Time_DenseTimeApproximationFromAbove_7f339f12
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:32:27.86309+00:00
-- url     : https://prove2.me/theorems/0836f898-5596-4f7f-9fea-f26c57a4ed59
-- title:
--   MarkovProcess: MarkovProcess_V3H_Time_DenseTimeApproximationFromAbove_7f339f12
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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


