-- Prove2me | Definitions.Def_SourceProof_99b77e5b4ba35572a6f0e4f6
-- name    : SourceProof_99b77e5b4ba35572a6f0e4f6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:33.411919+00:00
-- url     : https://prove2.me/theorems/ee892438-eb12-47a7-bab6-791eeb972b33
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.exists_gt_largeJumpSequence

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpSequence_F000
import Definitions.Def_SourceProof_1e736ec71ed59f8f581416d9
import Definitions.Def_SourceProof_b54ddf128850614ab86e8113
import Definitions.Def_SourceProof_fb98cafaf4269dae3b77bad4

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Enumeration of actual positive-time large jumps

The sequence starts at the first large jump strictly after zero, not at a zero sentinel. Every
finite entry is an actual positive-time jump larger than the threshold; finite entries never
repeat. Once infinity occurs it may repeat. Compact local finiteness forces the sequence to
escape each finite horizon, and the minimality of `nextLargeJump` proves that no large jump is
skipped. Thus an everywhere cadlag adapted process has an actual stopping-time enumeration,
with totally inaccessible entries whenever its positive jumps have that source property.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

variable {X : ℝ≥0 → Ω → ℝ} {b : ℝ} {ω : Ω}

namespace IsCadlagPath

theorem _root_.Prove2MeSourceProof.h_99b77e5b4ba35572a6f0e4f6 (hX : IsCadlagPath (X · ω))
    (hb : 0 < b) (T : ℝ≥0) : ∃ n : ℕ, (T : WithTop ℝ≥0) < largeJumpSequence X b n ω := by
  by_contra hnone
  push Not at hnone
  have hfin (n : ℕ) : ProbabilityTheory.largeJumpSequence X b n ω ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (hnone n)
  have hinj : Function.Injective (fun n ↦ ProbabilityTheory.largeJumpSequence X b n ω) := by
    intro n m hnm
    exact ((_root_.Prove2MeSourceProof.h_1e736ec71ed59f8f581416d9 hX) hb (hfin m)).mp hnm
  have hB : (((↑) : ℝ≥0 → WithTop ℝ≥0) ''
      {t : ℝ≥0 | 0 < t ∧ t ≤ T ∧ b < ‖ProbabilityTheory.jumpProcess X t ω‖}).Finite :=
    ((_root_.Prove2MeSourceProof.h_fb98cafaf4269dae3b77bad4 hX) T hb).image _
  have hfinite : (range (fun n ↦ ProbabilityTheory.largeJumpSequence X b n ω)).Finite := by
    apply hB.subset
    rintro z ⟨n, rfl⟩
    cases hn : ProbabilityTheory.largeJumpSequence X b n ω with
    | top => exact (hfin n hn).elim
    | coe t =>
      have ht := (_root_.Prove2MeSourceProof.h_b54ddf128850614ab86e8113 hX) hb hn
      refine ⟨t, ⟨ht.1, ?_, ht.2⟩, hn.symm⟩
      exact WithTop.coe_le_coe.mp (hn ▸ hnone n)
  exact (infinite_range_of_injective hinj) hfinite
end IsCadlagPath

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} {b : ℝ}

end ProbabilityTheory


