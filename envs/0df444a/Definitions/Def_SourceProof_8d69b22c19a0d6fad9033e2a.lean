-- Prove2me | Definitions.Def_SourceProof_8d69b22c19a0d6fad9033e2a
-- name    : SourceProof_8d69b22c19a0d6fad9033e2a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:08.123914+00:00
-- url     : https://prove2.me/theorems/f7e90538-6354-4638-a4df-93cab2315340
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.exists_local_norm_bound

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Local and compact bounds for caglad paths

Left continuity and finite right limits jointly give an ordinary neighborhood
bound, including at time zero. A compact subcover gives the finite-horizon bound.
-/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] {x : ℝ≥0 → E}

namespace IsCagladPath
theorem _root_.Prove2MeSourceProof.h_8d69b22c19a0d6fad9033e2a (hx : IsCagladPath x) (t : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in 𝓝 t, ‖x s‖ ≤ C := by
  obtain ⟨y, hy⟩ := hx.2 t
  have hl : ∀ᶠ s in 𝓝[≤] t, ‖x s‖ < ‖x t‖ + 1 :=
    (hx.1 t).norm.tendsto.eventually (Iio_mem_nhds (lt_add_one _))
  have hr : ∀ᶠ s in 𝓝[>] t, ‖x s‖ < ‖y‖ + 1 :=
    hy.norm.eventually (Iio_mem_nhds (lt_add_one _))
  refine ⟨max (‖x t‖ + 1) (‖y‖ + 1), by positivity, ?_⟩
  rw [← nhdsLE_sup_nhdsGT t, Filter.eventually_sup]
  exact ⟨hl.mono (fun _ hs ↦ hs.le.trans (le_max_left _ _)),
    hr.mono (fun _ hs ↦ hs.le.trans (le_max_right _ _))⟩
end IsCagladPath

end ProbabilityTheory


