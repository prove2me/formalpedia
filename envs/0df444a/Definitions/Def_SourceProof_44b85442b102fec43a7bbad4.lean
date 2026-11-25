-- Prove2me | Definitions.Def_SourceProof_44b85442b102fec43a7bbad4
-- name    : SourceProof_44b85442b102fec43a7bbad4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:37:57.334188+00:00
-- url     : https://prove2.me/theorems/a7b23a62-f024-5e45-8ca4-d47a9b5b2f76
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticCovariation_comm

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_F000
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_6f12ceaef9e4802a31ac72de

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Raw quadratic covariation by polarization of the canonical square bracket

This is the design's sole mixed bracket owner. It retains `X₀ Y₀`, is adapted
and cadlag, and has locally finite-variation paths. It is not asserted to be
increasing and is not a predictable compensator bracket.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_44b85442b102fec43a7bbad4
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.quadraticCovariation hY hF) (hY.quadraticCovariation hX hF) P := by
  have heq : ProbabilityTheory.Indistinguishable (X + Y) (Y + X) P :=
    ae_of_all _ fun ω t ↦ add_comm (X t ω) (Y t ω)
  filter_upwards [(_root_.Prove2MeSourceProof.h_6f12ceaef9e4802a31ac72de ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) hY)) ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hY) hX) hF heq] with ω hω t
  simp only [ProbabilityTheory.IsSemimartingale.quadraticCovariation, hω t]
  ring
end IsSemimartingale

end ProbabilityTheory


