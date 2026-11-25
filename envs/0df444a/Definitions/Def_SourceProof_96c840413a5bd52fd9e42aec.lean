-- Prove2me | Definitions.Def_SourceProof_96c840413a5bd52fd9e42aec
-- name    : SourceProof_96c840413a5bd52fd9e42aec
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:01.293704+00:00
-- url     : https://prove2.me/theorems/c76adaf8-dbf2-4ce8-b719-17922228a4d6
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.toProcess_repartition

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000
import Definitions.Def_SourceProof_335ae0b6c99b920a26294278
import Definitions.Def_SourceProof_45763a1547f08491c4364e73
import Definitions.Def_SourceProof_701610429fa16d24c6724a4a
import Definitions.Def_SourceProof_8f7895612117943074291d58
import Definitions.Def_SourceProof_93c5e92d913165554d4c657d
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417
import Definitions.Def_SourceProof_c1f91df6c360f9f8d687e8dd

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Repartitioning source simple predictable processes

The new coefficient is the old finite-step value immediately after the new left endpoint.
Its measurability is proved in that endpoint's stopping sigma-algebra. A genuine refinement
preserves the entire process and the elementary integral, including the independent time-zero
coefficient and all degenerate cells.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_96c840413a5bd52fd9e42aec (H : SimplePredictableRep F) {ρ : StoppingTimePartition F}
    (hρ : ρ.Refines H.partition) : (H.repartition ρ).toProcess = H.toProcess := by
  funext t ω
  by_cases ht : t = 0
  · subst t
    simp only [_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417]
    rfl
  by_cases hterm : t ≤ ρ.terminal ω
  · have hcell : ∃ i : Fin ρ.size, ρ.point i.castSucc ω < t ∧ t ≤ ρ.point i.succ ω :=
      (_root_.Prove2MeSourceProof.h_8f7895612117943074291d58 (ρ.path ω)) ⟨lt_of_le_of_ne bot_le (Ne.symm ht), hterm⟩
    obtain ⟨i, hi⟩ := hcell
    rw [(_root_.Prove2MeSourceProof.h_45763a1547f08491c4364e73 (i := i) (H.repartition ρ)) hi]
    change (∑ j : Fin H.partition.size,
      if H.partition.point j.castSucc ω ≤ ρ.point i.castSucc ω ∧
        ρ.point i.castSucc ω < H.partition.point j.succ ω then H.coefficient j ω else 0) = _
    rw [ProbabilityTheory.SimplePredictableRep.toProcess, if_neg ht]
    apply sum_congr rfl
    intro j _
    simp only [(_root_.Prove2MeSourceProof.h_93c5e92d913165554d4c657d hρ) hi j.castSucc, (_root_.Prove2MeSourceProof.h_701610429fa16d24c6724a4a hρ) hi j.succ]
  · have hρt : ρ.terminal ω < t := lt_of_not_ge hterm
    rw [(_root_.Prove2MeSourceProof.h_335ae0b6c99b920a26294278 (H.repartition ρ)) hρt,
      (_root_.Prove2MeSourceProof.h_335ae0b6c99b920a26294278 H) (((_root_.Prove2MeSourceProof.h_c1f91df6c360f9f8d687e8dd hρ) ω).trans_lt hρt)]
end ProbabilityTheory.SimplePredictableRep


