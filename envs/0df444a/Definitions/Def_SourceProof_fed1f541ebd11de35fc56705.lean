-- Prove2me | Definitions.Def_SourceProof_fed1f541ebd11de35fc56705
-- name    : SourceProof_fed1f541ebd11de35fc56705
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:26:53.654035+00:00
-- url     : https://prove2.me/theorems/d83474e4-51c9-465e-b993-6e8bf56ce3ef
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.mul_left_of_caglad

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_615a61300ee6a9f8d8759333
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact

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
theorem _root_.Prove2MeSourceProof.h_fed1f541ebd11de35fc56705 [IsFiniteMeasure P]
    {Z : ℕ → ℝ≥0 → Ω → ℝ} (hu : TendstoUCP P Z atTop Y)
    (hmZ : ∀ n t, Measurable (Z n t)) (hmY : ∀ t, Measurable (Y t))
    (hmH : ∀ t, Measurable (H t))
    (hrZ : ∀ n, HasCagladPaths (Z n) P) (hrY : HasCagladPaths Y P)
    (hrH : HasCagladPaths H P) :
    TendstoUCP P (fun n ↦ H * Z n) atTop (H * Y) := by
  simpa only [mul_comm] using (_root_.Prove2MeSourceProof.h_615a61300ee6a9f8d8759333 hu) hmZ hmY hmH hrZ hrY hrH
end TendstoUCP

end ProbabilityTheory


