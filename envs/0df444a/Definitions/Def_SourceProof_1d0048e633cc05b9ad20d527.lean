-- Prove2me | Definitions.Def_SourceProof_1d0048e633cc05b9ad20d527
-- name    : SourceProof_1d0048e633cc05b9ad20d527
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:09:52.935749+00:00
-- url     : https://prove2.me/theorems/e781cebb-2765-4816-9872-c4aa1e4ab2b5
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.eLpNorm_stochasticIntegral_le_of_bounded

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticIntegral_F000
import Definitions.Def_SourceProof_1658b3fb6ad99d5c993a7785
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_92ecc823f6e85260a04d51c7
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_d0a4533c9dc122ef1fd7f577
import Definitions.Def_SourceProof_da50a9b4aa24d95cd193edfb
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Lipschitz

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The bounded-integrand step of Protter II.20

Bounded simple approximation, the source second-moment estimate and actual
uniform-integrability limits give the finite-time L2 martingale result. Neither
the integrator nor the integral is centered by discarding its initial value.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_1d0048e633cc05b9ad20d527
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : Martingale X F P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (C : ℝ≥0)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖H t ω‖ ≤ C) (t : ℝ≥0) (hXt : MemLp (X t) 2 P) :
    eLpNorm (hX.stochasticIntegral hF ha hr t) 2 P ≤ C * eLpNorm (X t) 2 P := by
  obtain ⟨S, hS, hSb, huS⟩ := _root_.Prove2MeSourceProof.h_1658b3fb6ad99d5c993a7785 ha hF hr C hb
  have huJ := (_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF ha hr hS huS
  apply eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall fun n ↦
    (_root_.Prove2MeSourceProof.h_92ecc823f6e85260a04d51c7 (hS n)) hM hF
      (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) t hXt C (hSb n)) ((_root_.Prove2MeSourceProof.h_d0a4533c9dc122ef1fd7f577 huJ) t)
  intro n
  exact ((_root_.Prove2MeSourceProof.h_da50a9b4aa24d95cd193edfb (hS n)) hM hF
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) t hXt C (hSb n)).aestronglyMeasurable
end IsSemimartingale

end ProbabilityTheory


