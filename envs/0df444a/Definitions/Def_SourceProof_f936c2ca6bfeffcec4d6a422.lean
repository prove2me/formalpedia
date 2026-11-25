-- Prove2me | Definitions.Def_SourceProof_f936c2ca6bfeffcec4d6a422
-- name    : SourceProof_f936c2ca6bfeffcec4d6a422
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:57:20.426662+00:00
-- url     : https://prove2.me/theorems/5ae6b455-bfc9-507d-98e7-1b10407dadfb
-- title:
--   StochLean source theorem: ProbabilityTheory.IsTotalSemimartingale.congr_of_adapted

import Definitions.Def_SourceProof_5a4916e2e6cda9f70d628fae
import Definitions.Def_SourceProof_b7da9b0e051f7ca793d67cb5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Localization of source good integrators and semimartingales

Elementary integrals agree when entire integrator paths agree. This proves closure under
approximation outside sets of vanishing probability and then the local-to-global direction
for ordinary semimartingales, including the Protter time-zero mask.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsTotalSemimartingale
theorem _root_.Prove2MeSourceProof.h_f936c2ca6bfeffcec4d6a422 (hX : IsTotalSemimartingale X F P)
    (hXY : Indistinguishable X Y P) (ha : Adapted F Y) : IsTotalSemimartingale Y F P :=
  ⟨ha, _root_.Prove2MeSourceProof.h_5a4916e2e6cda9f70d628fae hXY hX.2.1, (_root_.Prove2MeSourceProof.h_b7da9b0e051f7ca793d67cb5 hX.2.2) hXY⟩
end IsTotalSemimartingale

variable [IsFiniteMeasure P]

end ProbabilityTheory


