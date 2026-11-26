-- Prove2me | Definitions.Def_SourceProof_fc24ae62259550d925059d44
-- name    : SourceProof_fc24ae62259550d925059d44
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:42:30.224505+00:00
-- url     : https://prove2.me/theorems/28c06444-7cd5-4e3a-a910-5c342037979f
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticCovariation_of_quadraticPureJump_left

import Definitions.Def_SourceProof_1d0b25291561423c84395ca8
import Definitions.Def_SourceProof_3266f92b2108293e91a89bfe

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
theorem _root_.Prove2MeSourceProof.h_fc24ae62259550d925059d44
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : hX.IsQuadraticPureJump hF) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (fun t ω ↦ X 0 ω * Y 0 ω +
        ∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_1d0b25291561423c84395ca8 hX) hY hF,
    (_root_.Prove2MeSourceProof.h_3266f92b2108293e91a89bfe hX) hY hF hQ]
    with ω hd hz t
  simpa only [hz t, Pi.zero_apply, add_zero] using (hd t).2
end IsSemimartingale

end ProbabilityTheory


