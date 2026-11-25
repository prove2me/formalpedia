-- Prove2me | Definitions.Def_SourceProof_ec912c886c06db43468f3a9e
-- name    : SourceProof_ec912c886c06db43468f3a9e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:46.451352+00:00
-- url     : https://prove2.me/theorems/f5d81579-104e-4ee3-b3e2-80e79c44afee
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.rightLimitProcess_toProcess

import Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F000
import Definitions.Def_SourceProof_f1a9e7d89c1df22dea8d5d1a
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Explicit right limits of the full source simple class

The independent initial spike disappears under the right-limit operation.
Every interval coefficient, including those on repeated endpoints, remains
in the exact finite formula with the right-continuous endpoint convention.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_ec912c886c06db43468f3a9e (H : SimplePredictableRep F) (t : ℝ≥0) (ω : Ω) :
    rightLimitProcess H.toProcess t ω = ∑ i : Fin H.partition.size,
      if H.partition.point i.castSucc ω ≤ t ∧ t < H.partition.point i.succ ω
      then H.coefficient i ω else 0 := by
  have hu := tendsto_finsetSum Finset.univ fun i _ ↦
    _root_.Prove2MeSourceProof.h_f1a9e7d89c1df22dea8d5d1a (H.partition.point i.castSucc ω)
      (H.partition.point i.succ ω) t (H.coefficient i ω)
  apply rightLim_eq_of_tendsto
  apply hu.congr'
  filter_upwards [self_mem_nhdsWithin] with u htu
  have hu0 : u ≠ 0 := ne_of_gt ((show (0 : ℝ≥0) ≤ t from bot_le).trans_lt htu)
  simp only [ProbabilityTheory.SimplePredictableRep.toProcess, if_neg hu0]
end ProbabilityTheory.SimplePredictableRep


