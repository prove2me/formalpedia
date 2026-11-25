-- Prove2me | Definitions.Def_SourceProof_a0cc4ed706abedad0ad223c1
-- name    : SourceProof_a0cc4ed706abedad0ad223c1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:23:46.340884+00:00
-- url     : https://prove2.me/theorems/8bf057c9-d510-5c68-bb80-cb6ec78cb9f7
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_indistinguishable_of_simple

import Definitions.Def_SourceProof_34df0ff9749e9285f8ed730b
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_60fbb0806e5cb393cb74e054
import Definitions.Def_SourceProof_932e1321dcffebeba90e2ea9
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c

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
theorem _root_.Prove2MeSourceProof.h_a0cc4ed706abedad0ad223c1
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (hH : IsSimplePredictable H F) :
    Indistinguishable (hX.stochasticIntegral hF ha hr) (hH.elementaryIntegralProcess X) P :=
  (_root_.Prove2MeSourceProof.h_34df0ff9749e9285f8ed730b hX) hF ha hr (fun _ ↦ hH)
    (_root_.Prove2MeSourceProof.h_60fbb0806e5cb393cb74e054 atTop H) (_root_.Prove2MeSourceProof.h_60fbb0806e5cb393cb74e054 atTop (hH.elementaryIntegralProcess X))
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_932e1321dcffebeba90e2ea9 hH) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)))
end IsSemimartingale

end ProbabilityTheory


