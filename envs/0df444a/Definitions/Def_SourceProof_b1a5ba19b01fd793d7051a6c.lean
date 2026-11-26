-- Prove2me | Definitions.Def_SourceProof_b1a5ba19b01fd793d7051a6c
-- name    : SourceProof_b1a5ba19b01fd793d7051a6c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:55:54.477432+00:00
-- url     : https://prove2.me/theorems/f2727058-3074-48bd-a6b7-7f61282598f1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticCovariation_initial_of_continuous_finiteVariation_right

import Definitions.Def_SourceProof_0dabfa92f51b3597c5e616f0
import Definitions.Def_SourceProof_44b85442b102fec43a7bbad4

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Mixed covariation of a quadratic pure-jump semimartingale

Protter II.28, with the library's raw initial-product convention. Positivity
of the continuous square bracket for all integer linear combinations forces
the continuous mixed bracket to vanish when either diagonal vanishes. The
countable intersection is taken before choosing a path or a time. The jump
series is the actual absolutely summable series, not a new bracket owner.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_b1a5ba19b01fd793d7051a6c
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths Y P) (hv : HasFiniteVariationPaths Y P) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (fun _ ω ↦ X 0 ω * Y 0 ω) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_44b85442b102fec43a7bbad4 hX) hY hF,
    (_root_.Prove2MeSourceProof.h_0dabfa92f51b3597c5e616f0 hY) hX hF hc hv]
    with ω hcomm hy t
  exact (hcomm t).trans ((hy t).trans (mul_comm _ _))
end IsSemimartingale

end ProbabilityTheory


