-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_TruncateSequence_F000
-- name    : StochLean_Probability_Process_Partition_TruncateSequence_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:59.584281+00:00
-- url     : https://prove2.me/theorems/ec88e262-9d5d-48e0-8445-e5e0fa91463f
-- title:
--   StochLean: Probability.Process.Partition.TruncateSequence F000

import Definitions.Def_StochLean_Probability_Process_Partition_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Definitions.Def_SourceProof_713ea2978da3b3a620edf296

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite capped partitions of an increasing stopping sequence

All `n` cells, including the first one, are retained. Stopping times may be infinite;
the finite cap gives everywhere-finite endpoints and repeated capped endpoints are legal.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

noncomputable def truncateSequence (τ : ℕ → Ω → WithTop ℝ≥0)
    (hτ : ∀ n, IsStoppingTime F (τ n)) (hm : ∀ ω, Monotone (τ · ω))
    (h0 : ∀ ω, τ 0 ω = 0) (n : ℕ) (T : ℝ≥0) : StoppingTimePartition F where
  size := n
  point := fun i ↦ FiniteStoppingTime.truncate (hτ i) T
  monotone_point := by
    intro ω i j hij
    apply WithTop.coe_le_coe.mp
    change (FiniteStoppingTime.truncate (hτ i) T).withTop ω ≤
      (FiniteStoppingTime.truncate (hτ j) T).withTop ω
    rw [_root_.Prove2MeSourceProof.h_713ea2978da3b3a620edf296, _root_.Prove2MeSourceProof.h_713ea2978da3b3a620edf296]
    exact min_le_min_left _ (hm ω hij)
  first_eq_zero := by
    intro ω
    apply WithTop.coe_eq_coe.mp
    change (FiniteStoppingTime.truncate (hτ 0) T).withTop ω = (0 : WithTop ℝ≥0)
    rw [_root_.Prove2MeSourceProof.h_713ea2978da3b3a620edf296]
    change min (T : WithTop ℝ≥0) (τ 0 ω) = (0 : WithTop ℝ≥0)
    rw [h0 ω]
    exact min_eq_right (WithTop.coe_le_coe.mpr (show (0 : ℝ≥0) ≤ T from bot_le))
variable (τ : ℕ → Ω → WithTop ℝ≥0) (hτ : ∀ n, IsStoppingTime F (τ n))
  (hm : ∀ ω, Monotone (τ · ω)) (h0 : ∀ ω, τ 0 ω = 0) (n : ℕ) (T : ℝ≥0)

end ProbabilityTheory.StoppingTimePartition


