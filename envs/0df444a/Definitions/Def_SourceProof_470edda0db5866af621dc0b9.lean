-- Prove2me | Definitions.Def_SourceProof_470edda0db5866af621dc0b9
-- name    : SourceProof_470edda0db5866af621dc0b9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:06:06.575704+00:00
-- url     : https://prove2.me/theorems/9ea1a904-354b-4fe8-a651-d83a1c7fdf0a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.hasCadlagPaths_stochasticIntegral

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticIntegral_F000
import Definitions.Def_SourceProof_ab0a4cce00e53a6efb5054a6

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
theorem _root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    HasCadlagPaths (hX.stochasticIntegral hF ha hr) P :=
  Eventually.of_forall ((_root_.Prove2MeSourceProof.h_ab0a4cce00e53a6efb5054a6 hX) hF ha hr)
end IsSemimartingale

end ProbabilityTheory


