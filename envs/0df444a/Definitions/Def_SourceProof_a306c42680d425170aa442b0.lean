-- Prove2me | Definitions.Def_SourceProof_a306c42680d425170aa442b0
-- name    : SourceProof_a306c42680d425170aa442b0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:01:40.222245+00:00
-- url     : https://prove2.me/theorems/498f0114-060b-4488-b7d0-d132f53b8e67
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.adapted_stochasticIntegral

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticIntegral_F000
import Definitions.Def_SourceProof_361655cd6ef42aa35eef5e59

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
theorem _root_.Prove2MeSourceProof.h_a306c42680d425170aa442b0
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Adapted F (hX.stochasticIntegral hF ha hr) :=
  ((_root_.Prove2MeSourceProof.h_361655cd6ef42aa35eef5e59 hX) hF ha hr).choose_spec.1
end IsSemimartingale

end ProbabilityTheory


