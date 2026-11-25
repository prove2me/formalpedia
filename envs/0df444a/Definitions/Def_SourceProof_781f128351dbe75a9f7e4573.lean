-- Prove2me | Definitions.Def_SourceProof_781f128351dbe75a9f7e4573
-- name    : SourceProof_781f128351dbe75a9f7e4573
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:17:50.420001+00:00
-- url     : https://prove2.me/theorems/90baf500-fc59-4fa8-adda-da72b53493e5
-- title:
--   StochLean source theorem: ProbabilityTheory.IsTotalSemimartingale.indicator_initial

import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Definitions.Def_SourceProof_96331e337c0a0b8560074745
import Definitions.Def_SourceProof_f5e68e551f95dbde3aa7e530

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Initial-event masks preserve source semimartingales

The good-integrator estimate is a direct outer-measure contraction. Adaptedness
uses only measurability of the event at time zero.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace IsTotalSemimartingale
theorem _root_.Prove2MeSourceProof.h_781f128351dbe75a9f7e4573 (hX : IsTotalSemimartingale X F P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    IsTotalSemimartingale (fun t ↦ s.indicator (X t)) F P :=
  ⟨(_root_.Prove2MeSourceProof.h_96331e337c0a0b8560074745 hX.1) hs, (_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 hX.2.1) s, (_root_.Prove2MeSourceProof.h_f5e68e551f95dbde3aa7e530 hX.2.2) s⟩
end IsTotalSemimartingale

end ProbabilityTheory


