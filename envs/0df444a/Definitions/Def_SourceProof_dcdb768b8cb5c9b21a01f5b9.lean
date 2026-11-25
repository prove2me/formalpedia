-- Prove2me | Definitions.Def_SourceProof_dcdb768b8cb5c9b21a01f5b9
-- name    : SourceProof_dcdb768b8cb5c9b21a01f5b9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:35:34.584952+00:00
-- url     : https://prove2.me/theorems/600a225a-0fde-4498-8073-61ea5a2da4eb
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.exists_local_norm_bound

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Local and compact bounds for cadlag paths

The lower endpoint is treated by right continuity alone. At positive times,
the actual finite left limit and right continuity give a neighborhood bound.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] {x : ℝ≥0 → E}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_dcdb768b8cb5c9b21a01f5b9 (hx : IsCadlagPath x) (t : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in 𝓝 t, ‖x s‖ ≤ C := by
  have hr : ∀ᶠ s in 𝓝[≥] t, ‖x s‖ < ‖x t‖ + 1 :=
    (hx.1 t).norm.tendsto.eventually (Iio_mem_nhds (lt_add_one _))
  by_cases ht : t = 0
  · subst t
    refine ⟨‖x 0‖ + 1, by positivity, ?_⟩
    simpa only [show Ici (0 : ℝ≥0) = univ from Ici_bot, nhdsWithin_univ] using
      hr.mono (fun _ hs ↦ hs.le)
  · obtain ⟨y, hy⟩ := hx.2 t ht
    have hl : ∀ᶠ s in 𝓝[<] t, ‖x s‖ < ‖y‖ + 1 :=
      hy.norm.eventually (Iio_mem_nhds (lt_add_one _))
    refine ⟨max (‖y‖ + 1) (‖x t‖ + 1), by positivity, ?_⟩
    rw [← nhdsLT_sup_nhdsGE t, Filter.eventually_sup]
    exact ⟨hl.mono (fun _ hs ↦ hs.le.trans (le_max_left _ _)),
      hr.mono (fun _ hs ↦ hs.le.trans (le_max_right _ _))⟩
end IsCadlagPath

end ProbabilityTheory


