-- Prove2me | Definitions.Def_SourceProof_dd381a297e552784125931ec
-- name    : SourceProof_dd381a297e552784125931ec
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:48:13.221913+00:00
-- url     : https://prove2.me/theorems/9d3be8fb-aadf-49c7-82c5-13b2514864c2
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticCovariation_comm

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_ContinuousPart_F000
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_b154264af403f6b2bc595390

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bilinearity of continuous covariation

The common-event raw identities and absolutely summable jump series give the
algebraic identities. No varying-integrator UCP continuity principle is assumed.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z X' Y' : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_dd381a297e552784125931ec
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.continuousQuadraticCovariation hY hF)
      (hY.continuousQuadraticCovariation hX hF) P := by
  have heq : ProbabilityTheory.Indistinguishable (X + Y) (Y + X) P :=
    ae_of_all _ fun ω t ↦ add_comm (X t ω) (Y t ω)
  filter_upwards [(_root_.Prove2MeSourceProof.h_b154264af403f6b2bc595390 ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) hY)) ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hY) hX) hF heq]
    with ω hω t
  simp only [ProbabilityTheory.IsSemimartingale.continuousQuadraticCovariation, hω t]
  ring
end IsSemimartingale

end ProbabilityTheory


