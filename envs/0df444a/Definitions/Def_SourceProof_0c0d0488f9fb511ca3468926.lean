-- Prove2me | Definitions.Def_SourceProof_0c0d0488f9fb511ca3468926
-- name    : SourceProof_0c0d0488f9fb511ca3468926
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:08:37.132528+00:00
-- url     : https://prove2.me/theorems/65322d6d-d065-4cae-bfc5-ee05a7a28daf
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticVariation_on_continuous_finiteVariation_paths

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_12d34a5d964556d97aab2788
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_3c52739457427316cb25bfbe
import Definitions.Def_SourceProof_42dda2460ed71edc7fce970c
import Definitions.Def_SourceProof_47027b6b170bba7ee3a3145f
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_846c7b04e1b31171d517724f
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The raw bracket on continuous finite-variation paths

The assertion is local to sample paths: the finite-variation event need not
have full measure. The initial square remains, even for a nonzero constant.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_0c0d0488f9fb511ca3468926
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, IsContinuousPath (X · ω) →
      LocallyBoundedVariationOn (X · ω) univ →
      ∀ t : ℝ≥0, hX.quadraticVariation hF t ω = (X 0 ω) ^ 2 := by
  let ha := (_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)
  let hr := (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
  filter_upwards [(_root_.Prove2MeSourceProof.h_42dda2460ed71edc7fce970c hX) hF ha hr]
    with ω hI hc hv
  obtain ⟨hωr, he⟩ := hI hv
  intro t
  have hi : StochLean.pathStieltjesIncrementIntegral (X · ω) hv hωr.1
      (ProbabilityTheory.leftLimitProcess X · ω) 0 t =
      StochLean.pathStieltjesIncrementIntegral (X · ω) hv hωr.1 (X · ω) 0 t := by
    apply _root_.Prove2MeSourceProof.h_47027b6b170bba7ee3a3145f
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (_root_.Prove2MeSourceProof.h_3c52739457427316cb25bfbe hc) (ne_of_gt hs.1)
  have hs := _root_.Prove2MeSourceProof.h_846c7b04e1b31171d517724f
    (hv := hv) (hr := hωr.1) (T := t) hc.continuousOn
  change X 0 ω * X 0 ω + StochLean.pathStieltjesIncrementIntegral (X · ω) hv hωr.1
    (X · ω) 0 t = ((X t ω) ^ 2 + (X 0 ω) ^ 2) / 2 at hs
  change (X t ω) ^ 2 - 2 * hX.stochasticIntegral hF ha hr t ω = (X 0 ω) ^ 2
  rw [he t]
  simp only [StochLean.pathStieltjesIntegral, _root_.Prove2MeSourceProof.h_12d34a5d964556d97aab2788, Pi.zero_apply, zero_mul, zero_add, hi]
  linarith
end IsSemimartingale

end ProbabilityTheory


