-- Prove2me | Definitions.Def_SourceProof_4100b78f80ce8fb249ea8a36
-- name    : SourceProof_4100b78f80ce8fb249ea8a36
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:43.340929+00:00
-- url     : https://prove2.me/theorems/4c1b6b39-cc45-45e9-9389-a740c95d6003
-- title:
--   StochLean source theorem: ProbabilityTheory.IsTotalSemimartingale.add

import Definitions.Def_SourceProof_f27f0406d0856e73dc290674
import Definitions.Def_SourceProof_fafcf0b157c21d22977aee5c

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

namespace IsTotalSemimartingale
theorem _root_.Prove2MeSourceProof.h_4100b78f80ce8fb249ea8a36 (hX : IsTotalSemimartingale X F P)
    (hY : IsTotalSemimartingale Y F P) : IsTotalSemimartingale (X + Y) F P :=
  ⟨fun t ↦ (hX.1 t).add (hY.1 t), (_root_.Prove2MeSourceProof.h_f27f0406d0856e73dc290674 hX.2.1) hY.2.1, (_root_.Prove2MeSourceProof.h_fafcf0b157c21d22977aee5c hX.2.2) hY.2.2⟩
end IsTotalSemimartingale

end ProbabilityTheory


