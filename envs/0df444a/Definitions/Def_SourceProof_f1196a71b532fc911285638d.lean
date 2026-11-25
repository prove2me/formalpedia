-- Prove2me | Definitions.Def_SourceProof_f1196a71b532fc911285638d
-- name    : SourceProof_f1196a71b532fc911285638d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:51:03.498695+00:00
-- url     : https://prove2.me/theorems/0562a85b-1567-50f8-8342-deddafecf65c
-- title:
--   StochLean source theorem: ProbabilityTheory.CompoundPoisson.law_apply

import Definitions.Def_SourceProof_afa4a77c82348c083f81d8eb
import Definitions.Def_SourceProof_f3db01ce3d4c266614f122be

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Compound Poisson laws

The construction is a genuine probability mixture: draw a Poisson count and then use the
corresponding convolution power of the jump law.  The zero-rate branch is proved explicitly and
does not depend on division by the intensity.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

namespace CompoundPoisson

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]


theorem _root_.Prove2MeSourceProof.h_f1196a71b532fc911285638d (r : ℝ≥0) (μ : ProbabilityMeasure G) {s : Set G}
    (hs : MeasurableSet s) :
    ((law r μ : ProbabilityMeasure G) : Measure G) s =
      ∫⁻ n, (ProbabilityMeasure.convPow μ n : Measure G) s ∂poissonMeasure r := by
  rw [_root_.Prove2MeSourceProof.h_afa4a77c82348c083f81d8eb, Measure.bind_apply hs (_root_.Prove2MeSourceProof.h_f3db01ce3d4c266614f122be μ).aemeasurable]
section CharacteristicFunction

end CharacteristicFunction

end CompoundPoisson

end ProbabilityTheory


