-- Prove2me | Definitions.Def_SourceProof_0dabfa92f51b3597c5e616f0
-- name    : SourceProof_0dabfa92f51b3597c5e616f0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:50:15.313394+00:00
-- url     : https://prove2.me/theorems/85f1d8bb-2791-5df2-ae0a-67d3207490d6
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticCovariation_initial_of_continuous_finiteVariation_left

import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_PureJump_F000
import Definitions.Def_SourceProof_3bb9a7fade1f7d012d20523e
import Definitions.Def_SourceProof_e6f3c2c77097f984cd91ae68
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
theorem _root_.Prove2MeSourceProof.h_0dabfa92f51b3597c5e616f0
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) (hv : HasFiniteVariationPaths X P) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (fun _ ω ↦ X 0 ω * Y 0 ω) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_e6f3c2c77097f984cd91ae68 hX) hY hF hv, hc]
    with ω he hx t
  rw [he t]
  have hz : (∑' s : Ioc 0 t, ProbabilityTheory.jumpProcess X s ω * ProbabilityTheory.jumpProcess Y s ω) = 0 := by
    calc
      _ = ∑' _s : Ioc 0 t, (0 : ℝ) := by
        apply tsum_congr
        intro s
        rw [(_root_.Prove2MeSourceProof.h_3bb9a7fade1f7d012d20523e hx) (ne_of_gt s.property.1), zero_mul]
      _ = 0 := tsum_zero
  exact (congrArg (X 0 ω * Y 0 ω + ·) hz).trans (add_zero _)
end IsSemimartingale

end ProbabilityTheory


