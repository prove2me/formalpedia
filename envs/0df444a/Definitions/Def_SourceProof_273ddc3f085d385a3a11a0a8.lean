-- Prove2me | Definitions.Def_SourceProof_273ddc3f085d385a3a11a0a8
-- name    : SourceProof_273ddc3f085d385a3a11a0a8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:56:38.509477+00:00
-- url     : https://prove2.me/theorems/0591007f-84a1-531f-956c-aa74dd4e32e6
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticCovariation_const_mul_right

import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_954e10b76576263a9def2e7a
import Definitions.Def_SourceProof_dd381a297e552784125931ec

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
theorem _root_.Prove2MeSourceProof.h_273ddc3f085d385a3a11a0a8
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) (c : ℝ) :
    Indistinguishable (hX.continuousQuadraticCovariation ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hY) c) hF)
      (c • hX.continuousQuadraticCovariation hY hF) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_dd381a297e552784125931ec hX) ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hY) c) hF,
    (_root_.Prove2MeSourceProof.h_954e10b76576263a9def2e7a hY) hX hF c,
    (_root_.Prove2MeSourceProof.h_dd381a297e552784125931ec hY) hX hF] with ω hcomm hmul hxy t
  simp only [hcomm t, hmul t, Pi.smul_apply, smul_eq_mul, hxy t]
end IsSemimartingale

end ProbabilityTheory


