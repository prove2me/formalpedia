-- Prove2me | Definitions.Def_SourceProof_f006d78a6e9979cf18230f20
-- name    : SourceProof_f006d78a6e9979cf18230f20
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:02:02.116836+00:00
-- url     : https://prove2.me/theorems/801e8a72-d3f6-47ac-9413-0d4e21d2a61d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.isCagladPath_leftLimitProcess

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_f17e21373c03eb2c377aaee1

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Source left limits and jumps

The Protter convention is `X_(0-) = 0`, not `X_0`. At positive times the
canonical Mathlib strict-left limit is reused; all mathematical limit identities
are proved on the cadlag domain. No limit property is asserted for an arbitrary
path on which a left limit does not exist.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_f006d78a6e9979cf18230f20 {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : IsCadlagPath (fun t ↦ X t ω)) :
    IsCagladPath (fun t ↦ leftLimitProcess X t ω) := by
  constructor
  · intro t
    by_cases ht : t = 0
    · subst t
      simpa only [show Set.Iic (0 : ℝ≥0) = {0} from Set.Iic_bot] using
        (continuousWithinAt_singleton (f := fun s ↦ ProbabilityTheory.leftLimitProcess X s ω) (x := 0))
    · have heq : (fun s ↦ Function.leftLim (fun u ↦ X u ω) s) =ᶠ[𝓝 t]
          fun s ↦ ProbabilityTheory.leftLimitProcess X s ω := by
        filter_upwards [Ioi_mem_nhds (pos_iff_ne_zero.mpr ht)] with s hs
        have hs' : 0 < s := hs
        simp only [ProbabilityTheory.leftLimitProcess, if_neg (ne_of_gt hs')]
      have hl := continuousWithinAt_leftLim_Iic (tendsto_leftLim_of_tendsto (h.2 t ht))
      exact hl.congr_of_eventuallyEq
        (heq.symm.filter_mono nhdsWithin_le_nhds) heq.self_of_nhds.symm
  · intro t
    refine ⟨X t ω, ?_⟩
    apply (_root_.Prove2MeSourceProof.h_f17e21373c03eb2c377aaee1 (h.1 t)).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hp : 0 < s := lt_of_le_of_lt bot_le hs
    simp only [ProbabilityTheory.leftLimitProcess, if_neg (ne_of_gt hp)]
end IsCadlagPath

end ProbabilityTheory


