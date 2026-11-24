-- Prove2me | Definitions.Def_SourceProof_3b9e1eacb18faa84cc0222f4
-- name    : SourceProof_3b9e1eacb18faa84cc0222f4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:35.447712+00:00
-- url     : https://prove2.me/theorems/cc90130a-d78e-430e-950d-77b474ab924c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.leftLim_pi

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_2904b8e06bc36e3ab7c34bfd

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Cadlag coordinate products and their actual left limits

The deterministic product property holds for arbitrary index types. The
common-event stochastic assertion requires countably many coordinates.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace ProbabilityTheory

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_3b9e1eacb18faa84cc0222f4 {ι : Type*} {x : ℝ≥0 → ι → ℝ}
    (hx : IsCadlagPath x) (t : ℝ≥0) : Function.leftLim x t = fun i ↦
      Function.leftLim (fun s ↦ x s i) t := by
  by_cases ht : t = 0
  · subst t
    simp only [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le)]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    apply leftLim_eq_of_tendsto
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_leftLim_of_tendsto ((_root_.Prove2MeSourceProof.h_2904b8e06bc36e3ab7c34bfd.mp hx i).2 t ht)
end IsCadlagPath

end ProbabilityTheory


