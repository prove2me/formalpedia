-- Prove2me | Definitions.Def_SourceProof_6ec6ed103d98506e37900b2a
-- name    : SourceProof_6ec6ed103d98506e37900b2a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:50:48.785798+00:00
-- url     : https://prove2.me/theorems/acc8e214-b4cd-56f5-a9d4-3ae8de4f9205
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.isTendingToIdentity_of_klenke

import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F005
import Definitions.Def_SourceProof_ad6533256e326b87026fa3d4
import Definitions.Def_SourceProof_f0d7366f281cd44e7eb0e371

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Klenke partitions as Protter stopping-time partitions

Finite restriction is lossless on each chosen horizon. This bridge imposes
neither a summable mesh rate nor new grid points inside a source cell.
It does not assert the still-separate general stochastic QV approximation.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

namespace StoppingTimePartition
theorem _root_.Prove2MeSourceProof.h_6ec6ed103d98506e37900b2a
    {π : ℕ → LocallyFinitePartition} (hπ : IsAdmissiblePartitionSequence π)
    {T : ℕ → ℝ≥0} (hT : Tendsto T atTop atTop) :
    IsTendingToIdentity (fun n ↦ deterministic F ((π n).restrict (T n))) P :=
  _root_.Prove2MeSourceProof.h_ad6533256e326b87026fa3d4 (fun n ↦ (π n).restrict (T n)) hT
    ((_root_.Prove2MeSourceProof.h_f0d7366f281cd44e7eb0e371 hπ) T)
end StoppingTimePartition

end ProbabilityTheory


