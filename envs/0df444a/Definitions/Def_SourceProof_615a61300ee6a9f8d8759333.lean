-- Prove2me | Definitions.Def_SourceProof_615a61300ee6a9f8d8759333
-- name    : SourceProof_615a61300ee6a9f8d8759333
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:10:05.717027+00:00
-- url     : https://prove2.me/theorems/596a9343-9715-551a-b8d0-531d16e9d2ec
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.mul_right_of_caglad

import Definitions.Def_SourceProof_43fbf96de532b2e4c5ed2cd2
import Definitions.Def_SourceProof_4f067a71c20982dfbf53ab5f
import Definitions.Def_SourceProof_523d7cde826eec51d63a0e17
import Definitions.Def_SourceProof_87b09384855fcec7a9387831
import Definitions.Def_SourceProof_944fa57bc3b71053cbab118a
import Definitions.Def_SourceProof_992997dcec9963390c8c98e7
import Definitions.Def_SourceProof_a307e422895411519841ce97
import Definitions.Def_SourceProof_d3a0db6a5b3b033e8d4b03a2
import Definitions.Def_SourceProof_feca862e0bd15cee9b184fdf
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # UCP multiplication by a fixed caglad process

The multiplier need only be pathwise bounded on compact intervals, not bounded
uniformly in the sample point or integrable. Countable dense deviations provide
the needed measurability, including an independent initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y H : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_615a61300ee6a9f8d8759333 [IsFiniteMeasure P]
    {Z : ℕ → ℝ≥0 → Ω → ℝ} (hu : TendstoUCP P Z atTop Y)
    (hmZ : ∀ n t, Measurable (Z n t)) (hmY : ∀ t, Measurable (Y t))
    (hmH : ∀ t, Measurable (H t))
    (hrZ : ∀ n, HasCagladPaths (Z n) P) (hrY : HasCagladPaths Y P)
    (hrH : HasCagladPaths H P) :
    TendstoUCP P (fun n ↦ Z n * H) atTop (Y * H) := by
  apply _root_.Prove2MeSourceProof.h_43fbf96de532b2e4c5ed2cd2
    (fun n T ↦ _root_.Prove2MeSourceProof.h_87b09384855fcec7a9387831
      (fun t ↦ (hmZ n t).mul (hmH t)) (fun t ↦ (hmY t).mul (hmH t))
      (_root_.Prove2MeSourceProof.h_feca862e0bd15cee9b184fdf ((_root_.Prove2MeSourceProof.h_523d7cde826eec51d63a0e17 (hrZ n)) hrH)) (_root_.Prove2MeSourceProof.h_feca862e0bd15cee9b184fdf ((_root_.Prove2MeSourceProof.h_523d7cde826eec51d63a0e17 hrY) hrH)) T)
  intro ns hns
  obtain ⟨k, _, hk⟩ := (_root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a ((_root_.Prove2MeSourceProof.h_a307e422895411519841ce97 hu) hns))
  refine ⟨k, ?_⟩
  filter_upwards [hk, hrH] with ω hω hHω
  intro T
  apply _root_.Prove2MeSourceProof.h_4f067a71c20982dfbf53ab5f (hω T)
  obtain ⟨C, _, hC⟩ := (_root_.Prove2MeSourceProof.h_d3a0db6a5b3b033e8d4b03a2 hHω) T
  exact ⟨C, fun t ht ↦ hC t ⟨bot_le, ht⟩⟩
end TendstoUCP

end ProbabilityTheory


