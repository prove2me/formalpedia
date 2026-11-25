-- Prove2me | Definitions.Def_SourceProof_63e1469ea21d6ee826860dba
-- name    : SourceProof_63e1469ea21d6ee826860dba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:36:14.129798+00:00
-- url     : https://prove2.me/theorems/8ecd41cb-37e0-5abc-a68e-412d49e8fa7d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.sub

import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_98b90b63a7c20b2905dd0848
import Definitions.Def_SourceProof_fafcf0b157c21d22977aee5c

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Negation and subtraction of source semimartingales -/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_63e1469ea21d6ee826860dba (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) :
    IsSemimartingale (X - Y) F P := by
  simpa only [sub_eq_add_neg] using (_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) (_root_.Prove2MeSourceProof.h_98b90b63a7c20b2905dd0848 hY)
end IsSemimartingale

end ProbabilityTheory


