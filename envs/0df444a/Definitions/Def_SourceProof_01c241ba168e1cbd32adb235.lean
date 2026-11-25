-- Prove2me | Definitions.Def_SourceProof_01c241ba168e1cbd32adb235
-- name    : SourceProof_01c241ba168e1cbd32adb235
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:24:40.782997+00:00
-- url     : https://prove2.me/theorems/29d5256d-8b2f-5953-a281-fbecda160ccf
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticCovariation_zero_on_left_zero_paths

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_PureJump_F000
import Definitions.Def_SourceProof_1baf76f2e8ee7f355f832ace
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_44f0559de53e8d14df7bb61f
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_a7b6b2ace97fad1531f4af27
import Definitions.Def_SourceProof_dd381a297e552784125931ec
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
theorem _root_.Prove2MeSourceProof.h_01c241ba168e1cbd32adb235
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, (∀ t, hX.continuousQuadraticVariation hF t ω = 0) →
      ∀ t, hX.continuousQuadraticCovariation hY hF t ω = 0 := by
  have hall : ∀ᵐ ω ∂P, ∀ z : ℤ, ∀ t,
      ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hY) ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) (z : ℝ))).continuousQuadraticVariation hF t ω =
        hY.continuousQuadraticVariation hF t ω +
          2 * (z : ℝ) * hY.continuousQuadraticCovariation hX hF t ω +
          (z : ℝ) ^ 2 * hX.continuousQuadraticVariation hF t ω :=
    ae_all_iff.mpr fun z ↦ (_root_.Prove2MeSourceProof.h_44f0559de53e8d14df7bb61f hY) hX hF (z : ℝ)
  filter_upwards [hall, (_root_.Prove2MeSourceProof.h_dd381a297e552784125931ec hX) hY hF]
    with ω ha hcomm hx t
  have hz : 2 * hY.continuousQuadraticCovariation hX hF t ω = 0 := by
    apply _root_.Prove2MeSourceProof.h_1baf76f2e8ee7f355f832ace
      (a := hY.continuousQuadraticVariation hF t ω)
    intro z
    have hp := (_root_.Prove2MeSourceProof.h_a7b6b2ace97fad1531f4af27 ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hY) ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) (z : ℝ)))) hF t ω
    rw [ha z t, hx t, mul_zero, add_zero] at hp
    nlinarith only [hp]
  rw [hcomm t]
  linarith
end IsSemimartingale

end ProbabilityTheory


