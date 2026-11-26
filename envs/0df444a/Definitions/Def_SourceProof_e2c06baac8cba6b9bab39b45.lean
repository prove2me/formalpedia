-- Prove2me | Definitions.Def_SourceProof_e2c06baac8cba6b9bab39b45
-- name    : SourceProof_e2c06baac8cba6b9bab39b45
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:53:30.093094+00:00
-- url     : https://prove2.me/theorems/eb4b6440-1bd3-577e-8014-33a72dbc8d83
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticCovariation_const_mul_right

import Definitions.Def_SourceProof_44b85442b102fec43a7bbad4
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_f3df3adc8be51e4f63a6abca

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bilinearity and version invariance of the canonical raw covariation

Linearity is inherited from the actual finite increment sums by uniqueness
of UCP limits. All comparisons are on one event for every time.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z X' Y' : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_e2c06baac8cba6b9bab39b45
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (c : ℝ) :
    Indistinguishable (hX.quadraticCovariation ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hY) c) hF)
      (c • hX.quadraticCovariation hY hF) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_44b85442b102fec43a7bbad4 hX) ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hY) c) hF,
    (_root_.Prove2MeSourceProof.h_f3df3adc8be51e4f63a6abca hY) hX hF c, (_root_.Prove2MeSourceProof.h_44b85442b102fec43a7bbad4 hY) hX hF]
    with ω hcomm hmul hxy t
  simp only [hcomm t, hmul t, Pi.smul_apply, smul_eq_mul, hxy t]
end IsSemimartingale

end ProbabilityTheory


