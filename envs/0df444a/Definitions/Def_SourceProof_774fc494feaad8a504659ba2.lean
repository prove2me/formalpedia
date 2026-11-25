-- Prove2me | Definitions.Def_SourceProof_774fc494feaad8a504659ba2
-- name    : SourceProof_774fc494feaad8a504659ba2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:36:55.6975+00:00
-- url     : https://prove2.me/theorems/079f4163-c39c-44cc-843e-6447cdd9518c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_masked_stoppedProcess

import Definitions.Def_SourceProof_3167c9529a23dc145fa8582c
import Definitions.Def_SourceProof_6ecb08b0ecac59b7f0cdb61a
import Definitions.Def_SourceProof_73c70764ff89ea6093f75bd8
import Definitions.Def_SourceProof_a239f509638bc9274841d0b5
import Definitions.Def_SourceProof_d11ad087607ea7f019708024
import Definitions.Def_SourceProof_e4b00545c150c0f6fcc1b938

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Initial masks commute with the constructed stochastic integral

The source initial term is included in both identities. Combining the identities
with stopping gives the exact masked local-property convention.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_774fc494feaad8a504659ba2
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable
      (((_root_.Prove2MeSourceProof.h_3167c9529a23dc145fa8582c ((_root_.Prove2MeSourceProof.h_6ecb08b0ecac59b7f0cdb61a hX) (hτ.measurableSet_gt 0))) hF hτ).stochasticIntegral
        hF ha hr)
      (MeasureTheory.stoppedProcess
        (fun t ↦ {ω | 0 < τ ω}.indicator (hX.stochasticIntegral hF ha hr t)) τ) P :=
  (_root_.Prove2MeSourceProof.h_73c70764ff89ea6093f75bd8 ((_root_.Prove2MeSourceProof.h_e4b00545c150c0f6fcc1b938 ((_root_.Prove2MeSourceProof.h_6ecb08b0ecac59b7f0cdb61a hX) (hτ.measurableSet_gt 0)))
    hF ha hr hτ))
    ((_root_.Prove2MeSourceProof.h_a239f509638bc9274841d0b5 ((_root_.Prove2MeSourceProof.h_d11ad087607ea7f019708024 hX) hF ha hr (hτ.measurableSet_gt 0))) τ)
end IsSemimartingale

end ProbabilityTheory


