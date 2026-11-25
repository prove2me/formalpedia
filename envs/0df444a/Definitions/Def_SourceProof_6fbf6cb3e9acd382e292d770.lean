-- Prove2me | Definitions.Def_SourceProof_6fbf6cb3e9acd382e292d770
-- name    : SourceProof_6fbf6cb3e9acd382e292d770
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:30:03.041359+00:00
-- url     : https://prove2.me/theorems/9370d2db-840c-446f-92bd-d9dc94baf815
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_masked_cutoff

import Definitions.Def_SourceProof_250eb65c80240d2467f59640
import Definitions.Def_SourceProof_73c70764ff89ea6093f75bd8
import Definitions.Def_SourceProof_7e3d78394bcbf6a774b5010b
import Definitions.Def_SourceProof_96331e337c0a0b8560074745
import Definitions.Def_SourceProof_a00c3775b630884a722167df
import Definitions.Def_SourceProof_d93b464447ac66fa122a70c4
import Definitions.Def_SourceProof_de3c03ff359f630b7abb9271
import Definitions.Def_SourceProof_dfba211aff959c1cb4116abf

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
theorem _root_.Prove2MeSourceProof.h_6fbf6cb3e9acd382e292d770
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable
      (hX.stochasticIntegral hF
        ((_root_.Prove2MeSourceProof.h_96331e337c0a0b8560074745 (_root_.Prove2MeSourceProof.h_dfba211aff959c1cb4116abf ha hτ)) (hτ.measurableSet_gt 0))
        ((_root_.Prove2MeSourceProof.h_d93b464447ac66fa122a70c4 ((_root_.Prove2MeSourceProof.h_250eb65c80240d2467f59640 hr) τ)) {ω | 0 < τ ω}))
      (MeasureTheory.stoppedProcess
        (fun t ↦ {ω | 0 < τ ω}.indicator (hX.stochasticIntegral hF ha hr t)) τ) P := by
  rw [stoppedProcess_indicator_comm']
  exact (_root_.Prove2MeSourceProof.h_73c70764ff89ea6093f75bd8 ((_root_.Prove2MeSourceProof.h_a00c3775b630884a722167df hX) hF (_root_.Prove2MeSourceProof.h_dfba211aff959c1cb4116abf ha hτ)
    ((_root_.Prove2MeSourceProof.h_250eb65c80240d2467f59640 hr) τ) (hτ.measurableSet_gt 0)))
    ((_root_.Prove2MeSourceProof.h_de3c03ff359f630b7abb9271 ((_root_.Prove2MeSourceProof.h_7e3d78394bcbf6a774b5010b hX) hF ha hr hτ)) {ω | 0 < τ ω})
end IsSemimartingale

end ProbabilityTheory


