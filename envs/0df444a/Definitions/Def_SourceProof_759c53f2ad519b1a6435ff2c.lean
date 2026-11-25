-- Prove2me | Definitions.Def_SourceProof_759c53f2ad519b1a6435ff2c
-- name    : SourceProof_759c53f2ad519b1a6435ff2c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:11:44.989004+00:00
-- url     : https://prove2.me/theorems/61876bf2-84d6-4da3-8285-7d032b272936
-- title:
--   StochLean source theorem: ProbabilityTheory.tendsto_strictLeftGrid

import Definitions.Def_SourceProof_2f98b91a3aee037c28e77064
import Definitions.Def_SourceProof_fcbf5f956343bc904f2e8dd0

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Strict-past deterministic grids for predictable processes

At a positive grid endpoint the preceding cell is used, as required for predictable
`(s,t]` rectangles. At zero the original initial value is retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_759c53f2ad519b1a6435ff2c (t : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ strictLeftGrid (1 / ((n : ℝ≥0) + 1)) t) atTop (𝓝[≤] t) := by
  have hδ : ∀ n : ℕ, 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) := fun n ↦ by positivity
  have hlim : Tendsto (fun n : ℕ ↦ (1 : ℝ≥0) / ((n : ℝ≥0) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall (fun n ↦ _root_.Prove2MeSourceProof.h_fcbf5f956343bc904f2e8dd0 (hδ n) t)⟩
  have hlo : Tendsto (fun n : ℕ ↦ t - 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 t) := by
    simpa only [tsub_zero] using tendsto_const_nhds.sub hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun n ↦ tsub_le_iff_right.mpr (_root_.Prove2MeSourceProof.h_2f98b91a3aee037c28e77064 (hδ n) t))
    (fun n ↦ _root_.Prove2MeSourceProof.h_fcbf5f956343bc904f2e8dd0 (hδ n) t)
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

end MeasureTheory


