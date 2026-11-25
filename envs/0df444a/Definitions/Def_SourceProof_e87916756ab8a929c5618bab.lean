-- Prove2me | Definitions.Def_SourceProof_e87916756ab8a929c5618bab
-- name    : SourceProof_e87916756ab8a929c5618bab
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:15:26.923822+00:00
-- url     : https://prove2.me/theorems/5e50903c-e8cf-4c78-936c-064abd42bd82
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLocalMartingale.neg

import Definitions.Def_SourceProof_7db93d1355c7ca503c2bcbae

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Stopping and linear stability of Protter local martingales

Fundamental sequences are actual witnesses. A shared localizer is the pointwise
minimum of two existing localizers. Its time-zero mask is the intersection of
their masks; the unmasked Klenke definition is not silently substituted.

Source: Protter I.48 (stopping and linear operations).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

namespace IsLocalMartingale
theorem _root_.Prove2MeSourceProof.h_e87916756ab8a929c5618bab (hX : IsLocalMartingale X F P) :
    IsLocalMartingale (-X) F P := by simpa only [neg_one_smul] using (_root_.Prove2MeSourceProof.h_7db93d1355c7ca503c2bcbae hX) (-1)
end IsLocalMartingale

end ProbabilityTheory


