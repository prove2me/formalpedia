-- Prove2me | Definitions.Def_SourceProof_bfeed756142db6bfc4af483e
-- name    : SourceProof_bfeed756142db6bfc4af483e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:22:38.794689+00:00
-- url     : https://prove2.me/theorems/33c3671c-65be-4e6e-a950-867341a652db
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.isCadlag_largeJumpResidual

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpResidual_F000
import Definitions.Def_SourceProof_c3fe4883c07b4b4f52cda50c

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual finite-prefix large-jump residuals

The residual removes exactly the first `K` entries of the actual large-jump sequence.
At infinite entries the coefficient is explicitly zero. On the measurable coverage
event all its positive-time jumps on the horizon are small. Fixed-cap short-window
moments are derived from this event, whose complement tends to zero in probability.
No integrability of a random total jump count is required.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

variable {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {b : ℝ}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_bfeed756142db6bfc4af483e (hX : IsCadlagPath (X · ω)) (b : ℝ) (K : ℕ) :
    IsCadlagPath (fun t ↦ largeJumpResidual X b K t ω) :=
  (_root_.Prove2MeSourceProof.h_c3fe4883c07b4b4f52cda50c hX) (Finset.range K) (ProbabilityTheory.largeJumpSequence X b)
    (fun i ↦ MeasureTheory.stoppedValueWithTerminal (ProbabilityTheory.jumpProcess X) (fun _ ↦ (0 : ℝ))
      (ProbabilityTheory.largeJumpSequence X b i))
end IsCadlagPath

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

end MeasureTheory


