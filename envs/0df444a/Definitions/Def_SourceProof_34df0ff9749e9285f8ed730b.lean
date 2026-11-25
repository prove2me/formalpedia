-- Prove2me | Definitions.Def_SourceProof_34df0ff9749e9285f8ed730b
-- name    : SourceProof_34df0ff9749e9285f8ed730b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:19:28.702813+00:00
-- url     : https://prove2.me/theorems/e759c868-56cd-4016-bc93-d30a01a36eb2
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_indistinguishable_of_limit

import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_ae584a9168b1bd16f954b4f8
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The source Chapter II stochastic integral

This is the unique cadlag UCP limit of source elementary integrals, up to
indistinguishability. The selector is only available for a semimartingale
integrator and an adapted, common-event caglad integrand under usual conditions.
It is not a Chapter IV integral for arbitrary predictable processes.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale

theorem _root_.Prove2MeSourceProof.h_34df0ff9749e9285f8ed730b
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {S : ℕ → ℝ≥0 → Ω → ℝ} (hS : ∀ n, IsSimplePredictable (S n) F)
    (hu : TendstoUCP P S atTop H) {J : ℝ≥0 → Ω → ℝ}
    (hJ : TendstoUCP P (fun n ↦ (hS n).elementaryIntegralProcess X) atTop J)
    (hrJ : HasRightContinuousPaths J P) :
    Indistinguishable (hX.stochasticIntegral hF ha hr) J P :=
  (_root_.Prove2MeSourceProof.h_ae584a9168b1bd16f954b4f8 ((_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF ha hr hS hu)) hJ
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF ha hr)) hrJ
end IsSemimartingale

end ProbabilityTheory


