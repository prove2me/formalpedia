-- Prove2me | Definitions.Def_SourceProof_f4396e898db7f84ef35db80b
-- name    : SourceProof_f4396e898db7f84ef35db80b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:53:04.467798+00:00
-- url     : https://prove2.me/theorems/53c972b5-1a72-4c76-92ce-5fc23aae16e1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.finset_sum

import Definitions.Def_SourceProof_0f1f1b63b3e52165c8596e25
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_fafcf0b157c21d22977aee5c

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite sums of good-integrator semimartingales -/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_f4396e898db7f84ef35db80b {Ω κ : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : κ → ℝ≥0 → Ω → ℝ} (s : Finset κ)
    (hX : ∀ i ∈ s, IsSemimartingale (X i) F P) :
    IsSemimartingale (∑ i ∈ s, X i) F P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [sum_empty, Pi.zero_def] using
      (_root_.Prove2MeSourceProof.h_0f1f1b63b3e52165c8596e25 (F := F) (P := P)
        (Z := fun _ ↦ (0 : ℝ)) measurable_const)
  | @insert i s hi ih =>
    rw [sum_insert hi]
    exact (_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d (hX i (mem_insert_self _ _)))
      (ih (fun j hj ↦ hX j (mem_insert_of_mem hj)))
end IsSemimartingale

end ProbabilityTheory


