-- Prove2me | Definitions.Def_SourceProof_3266f92b2108293e91a89bfe
-- name    : SourceProof_3266f92b2108293e91a89bfe
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:33:47.569178+00:00
-- url     : https://prove2.me/theorems/1370ee2d-f87f-4b9b-b906-7d6c1b26522b
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticCovariation_zero_of_quadraticPureJump_left

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_ContinuousPart_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_PureJump_F000
import Definitions.Def_SourceProof_01c241ba168e1cbd32adb235
import Mathlib.Algebra.Order.Archimedean.Real.Basic

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
theorem _root_.Prove2MeSourceProof.h_3266f92b2108293e91a89bfe
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : hX.IsQuadraticPureJump hF) :
    Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_01c241ba168e1cbd32adb235 hX) hY hF, hQ]
    with ω hz hx t
  exact hz hx t
end IsSemimartingale

end ProbabilityTheory


