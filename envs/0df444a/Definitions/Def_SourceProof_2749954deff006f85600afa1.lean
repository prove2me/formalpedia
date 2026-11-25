-- Prove2me | Definitions.Def_SourceProof_2749954deff006f85600afa1
-- name    : SourceProof_2749954deff006f85600afa1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:15:42.883118+00:00
-- url     : https://prove2.me/theorems/7ef8ae4f-9ccd-5a97-bfba-0585b96e1ff8
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.finset_sum

import Definitions.Def_SourceProof_2788bc818189572242b6cda6
import Definitions.Def_SourceProof_50bef199e170152e0882c89e
import Definitions.Def_SourceProof_669e70af113890cd7317fc66
import Definitions.Def_SourceProof_f27f0406d0856e73dc290674
import Mathlib.Analysis.Normed.Group.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Caglad initial spikes and left-open, right-closed step paths -/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

namespace IsCagladPath
theorem _root_.Prove2MeSourceProof.h_2749954deff006f85600afa1 {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0 → ℝ)
    (hf : ∀ i ∈ s, IsCagladPath (f i)) : IsCagladPath (fun t ↦ ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (_root_.Prove2MeSourceProof.h_50bef199e170152e0882c89e (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (_root_.Prove2MeSourceProof.h_2788bc818189572242b6cda6 (hf a (Finset.mem_insert_self _ _)))
        (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))
end IsCagladPath

end ProbabilityTheory


