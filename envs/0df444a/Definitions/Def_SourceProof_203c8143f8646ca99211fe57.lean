-- Prove2me | Definitions.Def_SourceProof_203c8143f8646ca99211fe57
-- name    : SourceProof_203c8143f8646ca99211fe57
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:00:59.290725+00:00
-- url     : https://prove2.me/theorems/16e97402-498d-4dca-88d4-119da1612836
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.finset_sum

import Definitions.Def_SourceProof_a2cb63993a652b5632791121
import Definitions.Def_SourceProof_d80df7975aaa241a180afe6d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous operations on cadlag and caglad paths

The process statements intersect finitely many common full-measure events.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {T Ω E G : Type*} [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace E] [TopologicalSpace G] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {X Y : T → Ω → E}

variable [OrderBot T]

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_203c8143f8646ca99211fe57 [AddCommMonoid E] [ContinuousAdd E]
    {ι : Type*} (s : Finset ι) (f : ι → T → E)
    (hf : ∀ i ∈ s, IsCadlagPath (f i)) : IsCadlagPath (fun t ↦ ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (_root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121
      (continuous_const : Continuous (fun _ : T ↦ (0 : E))))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (_root_.Prove2MeSourceProof.h_d80df7975aaa241a180afe6d (hf i (Finset.mem_insert_self i s)))
      (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))
end IsCadlagPath

end ProbabilityTheory


