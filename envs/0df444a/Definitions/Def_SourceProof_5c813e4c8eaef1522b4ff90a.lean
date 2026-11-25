-- Prove2me | Definitions.Def_SourceProof_5c813e4c8eaef1522b4ff90a
-- name    : SourceProof_5c813e4c8eaef1522b4ff90a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:26:51.170205+00:00
-- url     : https://prove2.me/theorems/62a60d6e-1e95-5ab1-94e0-fd1f1b80bdda
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLocalMartingale.sub

import Definitions.Def_SourceProof_e87916756ab8a929c5618bab
import Definitions.Def_SourceProof_fe291c44e887541ef919a656

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
theorem _root_.Prove2MeSourceProof.h_5c813e4c8eaef1522b4ff90a (hX : IsLocalMartingale X F P)
    (hY : IsLocalMartingale Y F P) (hF : F.IsUsual P) :
    IsLocalMartingale (X - Y) F P := by
  simpa only [sub_eq_add_neg] using (_root_.Prove2MeSourceProof.h_fe291c44e887541ef919a656 hX) (_root_.Prove2MeSourceProof.h_e87916756ab8a929c5618bab hY) hF
end IsLocalMartingale

end ProbabilityTheory


