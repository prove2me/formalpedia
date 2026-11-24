-- Prove2me | Definitions.Def_SourceProof_215f6d5e6b10999a8c8f10ba
-- name    : SourceProof_215f6d5e6b10999a8c8f10ba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:25:57.492259+00:00
-- url     : https://prove2.me/theorems/a4a04fbc-ebad-432d-b268-4ec05fdb22fc
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.IsTendingToIdentity.tendstoUCP_min_terminal

import Definitions.Def_StochLean_Probability_Process_Partition_F001
import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_41f7a8bc90f81c6d1f4646aa
import Mathlib.MeasureTheory.Integral.Indicator

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # UCP exhaustion by finite stopping endpoints

On each compact interval, stopping eventually changes nothing on almost every
path. Measurable endpoint events bound the possibly nonmeasurable deviation
events, so no regularity or measurability assumption on the process is needed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

namespace StoppingTimePartition
namespace IsTendingToIdentity
theorem _root_.Prove2MeSourceProof.h_215f6d5e6b10999a8c8f10ba
    {F : Filtration ℝ≥0 mΩ} {π : ℕ → StoppingTimePartition F}
    (hπ : StoppingTimePartition.IsTendingToIdentity π P) (X : ℝ≥0 → Ω → ℝ) :
    TendstoUCP P (fun n t ω ↦ X (min ((π n).terminal ω) t) ω) atTop X := by
  apply _root_.Prove2MeSourceProof.h_41f7a8bc90f81c6d1f4646aa _ (hπ.mono fun _ hω ↦ hω.1) X
  intro n T
  have h := ((π n).terminal.isStoppingTime.measurableSet_lt T)
  exact (F.le T) _ (by simpa only [WithTop.coe_lt_coe] using h)
end IsTendingToIdentity
end StoppingTimePartition

end ProbabilityTheory


