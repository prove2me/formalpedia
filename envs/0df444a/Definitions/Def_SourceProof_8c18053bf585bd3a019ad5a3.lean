-- Prove2me | Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
-- name    : SourceProof_8c18053bf585bd3a019ad5a3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:20:37.889441+00:00
-- url     : https://prove2.me/theorems/9bd45074-e15b-5748-9ad9-9e2b76c3a4c4
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.const_mul

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_db083938190d317e3f66eea4
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
theorem _root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 (hX : IsSemimartingale X F P) (c : ℝ) :
    IsSemimartingale (fun t ω ↦ c * X t ω) F P := by
  intro t
  exact (_root_.Prove2MeSourceProof.h_db083938190d317e3f66eea4 (hX t)) c
end IsSemimartingale

end ProbabilityTheory


