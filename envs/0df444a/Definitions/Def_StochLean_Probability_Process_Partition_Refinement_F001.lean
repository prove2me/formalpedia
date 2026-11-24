-- Prove2me | Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F001
-- name    : StochLean_Probability_Process_Partition_Refinement_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:21.072183+00:00
-- url     : https://prove2.me/theorems/b5aadfc3-b455-42f8-a400-27a257ea58a8
-- title:
--   StochLean: Probability.Process.Partition.Refinement F001

import Definitions.Def_StochLean_Probability_Process_Partition_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_SourceProof_136c18157609b41bd9beb303
import Definitions.Def_SourceProof_aa8bccb9399de6b4088d30d9
import Definitions.Def_SourceProof_cf64c9a6c7f0a6a27abe12f0
import Mathlib.Data.Fin.Tuple.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Common refinements of finite stopping-time partitions

Refinement is pathwise endpoint inclusion, so random coincidences and repeated endpoints
are allowed. Splitting at one finite stopping time uses only minima and maxima of stopping
times. The witness construction is deliberately nonminimal; it requires no measurable sorting
choice and does not impose boundedness or additional conditions on the filtration.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

/-- The first block is capped at `τ`; the second block is raised to `τ`.
The possible gap between the blocks will carry a zero coefficient. -/
def splitAt (π : StoppingTimePartition F) (τ : FiniteStoppingTime F) :
    StoppingTimePartition F where
  size := π.size + 1 + π.size
  point := Fin.append (m := π.size + 1) (n := π.size + 1)
    (fun i ↦ (π.point i).min τ) (fun i ↦ (π.point i).max τ)
  monotone_point := by
    intro ω
    refine Fin.addCases (m := π.size + 1) (n := π.size + 1) (fun i ↦ ?_) (fun i ↦ ?_)
    · refine Fin.addCases (m := π.size + 1) (n := π.size + 1)
        (fun j hij ↦ ?_) (fun j _ ↦ ?_)
      · simp only [Fin.append_left, _root_.Prove2MeSourceProof.h_136c18157609b41bd9beb303]
        exact min_le_min_right _ (π.monotone_point ω (by exact hij))
      · simp only [Fin.append_left, Fin.append_right, _root_.Prove2MeSourceProof.h_136c18157609b41bd9beb303,
          _root_.Prove2MeSourceProof.h_cf64c9a6c7f0a6a27abe12f0]
        exact (min_le_right _ _).trans (le_max_right _ _)
    · refine Fin.addCases (m := π.size + 1) (n := π.size + 1)
        (fun j hij ↦ ?_) (fun j hij ↦ ?_)
      · have hi := i.isLt
        have hj := j.isLt
        simp only [Fin.le_def, Fin.val_natAdd, Fin.val_castAdd] at hij
        omega
      · simp only [Fin.append_right, _root_.Prove2MeSourceProof.h_cf64c9a6c7f0a6a27abe12f0]
        exact max_le_max_right _ (π.monotone_point ω (by simpa using hij))
  first_eq_zero := by
    intro ω
    change Fin.append (α := FiniteStoppingTime F) _ _
      ((0 : Fin (π.size + 1)).castAdd (π.size + 1)) ω = 0
    simp only [Fin.append_left, _root_.Prove2MeSourceProof.h_136c18157609b41bd9beb303, π.first_eq_zero]
    exact min_eq_left bot_le
end ProbabilityTheory.StoppingTimePartition


