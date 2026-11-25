-- Prove2me | Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e
-- name    : SourceProof_e327ffe5c9d18f0324a2ad4e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:58:03.940988+00:00
-- url     : https://prove2.me/theorems/54f389f0-0e2b-5834-a98a-adc2efaebeef
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.tendstoUCP_stochasticIntegral_of_simple

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
theorem _root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {S : ℕ → ℝ≥0 → Ω → ℝ} (hS : ∀ n, IsSimplePredictable (S n) F)
    (hu : TendstoUCP P S atTop H) :
    TendstoUCP P (fun n ↦ (hS n).elementaryIntegralProcess X) atTop
      (hX.stochasticIntegral hF ha hr) :=
  ((_root_.Prove2MeSourceProof.h_361655cd6ef42aa35eef5e59 hX) hF ha hr).choose_spec.2.2 S hS hu
end IsSemimartingale

end ProbabilityTheory


