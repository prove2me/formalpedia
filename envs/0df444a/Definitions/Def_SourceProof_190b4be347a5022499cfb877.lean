-- Prove2me | Definitions.Def_SourceProof_190b4be347a5022499cfb877
-- name    : SourceProof_190b4be347a5022499cfb877
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:19:53.70488+00:00
-- url     : https://prove2.me/theorems/43072b7b-a962-5551-bdf8-2cf290db68aa
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCagladPath.tendsto_hittingAfter_norm_nat

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_FirstExitTruncation_F000
import Definitions.Def_SourceProof_d3a0db6a5b3b033e8d4b03a2
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded masked cutoffs of adapted caglad processes

Open norm exits need not attain their target. Compact path bounds prove divergence
without an attainment claim. The closed cutoff remains bounded at a positive exit
by left continuity; the initial mask handles arbitrary initial values.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {H : ℝ≥0 → Ω → ℝ}

namespace IsCagladPath
theorem _root_.Prove2MeSourceProof.h_190b4be347a5022499cfb877 {ω : Ω}
    (hH : IsCagladPath (H · ω)) :
    Tendsto (fun n : ℕ ↦ hittingAfter H {x | (n : ℝ) < ‖x‖} 0 ω) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro T
  obtain ⟨C, _, hC⟩ := (_root_.Prove2MeSourceProof.h_d3a0db6a5b3b033e8d4b03a2 hH) (T + 1)
  obtain ⟨N, hN⟩ := exists_nat_gt C
  filter_upwards [eventually_ge_atTop N] with n hn
  have hbound : (T + 1 : ℝ≥0) ≤ hittingAfter H {x | (n : ℝ) < ‖x‖} 0 ω := by
    by_contra h
    obtain ⟨t, ht, hhit⟩ := hittingAfter_lt_iff.mp (lt_of_not_ge h)
    have htC := hC t ⟨ht.1, ht.2.le⟩
    exact (not_lt_of_ge htC) (hN.trans_le (Nat.cast_le.mpr hn) |>.trans hhit)
  exact (WithTop.coe_lt_coe.mpr (lt_add_one T)).trans_le hbound
end IsCagladPath

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

end MeasureTheory


