-- Prove2me | Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
-- name    : SourceProof_31d0de13ef1656df97c05a7d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:44:58.085816+00:00
-- url     : https://prove2.me/theorems/ff627bf5-6889-4ae4-b0f5-3e23cc4ce697
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.add

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_4100b78f80ce8fb249ea8a36
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Linear stability of the source good-integrator predicate

These results use elementary integration and its quantitative continuity
criterion. No classical decomposition or Bichteler-Dellacherie theorem is
assumed in proving stability.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) :
    IsSemimartingale (X + Y) F P := by
  intro t
  exact (_root_.Prove2MeSourceProof.h_4100b78f80ce8fb249ea8a36 (hX t)) (hY t)
end IsSemimartingale

end ProbabilityTheory


