-- Prove2me | Definitions.Def_SourceProof_e6f3c2c77097f984cd91ae68
-- name    : SourceProof_e6f3c2c77097f984cd91ae68
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:40:11.95624+00:00
-- url     : https://prove2.me/theorems/79e0606c-b0a9-599b-b4dc-74328739df76
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticCovariation_of_finiteVariation_left

import Definitions.Def_SourceProof_85f099f7bded05568c0ca1c5
import Definitions.Def_SourceProof_fc24ae62259550d925059d44
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

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
theorem _root_.Prove2MeSourceProof.h_e6f3c2c77097f984cd91ae68
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths X P) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (fun t ω ↦ X 0 ω * Y 0 ω +
        ∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) P :=
  (_root_.Prove2MeSourceProof.h_fc24ae62259550d925059d44 hX) hY hF
    ((_root_.Prove2MeSourceProof.h_85f099f7bded05568c0ca1c5 hX) hF hv)
end IsSemimartingale

end ProbabilityTheory


