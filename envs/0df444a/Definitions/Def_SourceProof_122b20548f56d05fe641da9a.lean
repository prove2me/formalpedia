-- Prove2me | Definitions.Def_SourceProof_122b20548f56d05fe641da9a
-- name    : SourceProof_122b20548f56d05fe641da9a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:47:15.119274+00:00
-- url     : https://prove2.me/theorems/738dca2f-a384-588b-be65-57eeb3c5b9da
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousLocalMartingale.locally_squareIntegrableMartingale

import Definitions.Def_SourceProof_adff851f13316a352bc1b23e
import Definitions.Def_SourceProof_ff61f6e818da41b2b20b8dc5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous local martingales are locally square integrable

The canonical Protter mask handles arbitrary finite, possibly nonintegrable initial values.
Intersect the centered level localizer with the initial-value localizer. Each masked stopped
process is bounded, UI, and square integrable at every finite time. No unmasked L2 assertion
is made without the necessary initial-value hypothesis.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

namespace IsContinuousLocalMartingale
theorem _root_.Prove2MeSourceProof.h_122b20548f56d05fe641da9a
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F X P := by
  obtain ⟨τ, hτ, hb⟩ := (_root_.Prove2MeSourceProof.h_ff61f6e818da41b2b20b8dc5 hX) hF
  exact ⟨τ, (_root_.Prove2MeSourceProof.h_adff851f13316a352bc1b23e hτ), fun n ↦ (hb n).2⟩
end IsContinuousLocalMartingale

end ProbabilityTheory


