-- Prove2me | Definitions.Def_SourceProof_996b5538f02fe4ec38c5a73c
-- name    : SourceProof_996b5538f02fe4ec38c5a73c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:58:10.489026+00:00
-- url     : https://prove2.me/theorems/f235de39-6941-5827-a08f-14854db41589
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticVariation_zero_on_finiteVariation_paths

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Definitions.Def_SourceProof_7a2cd734cad19a873789e942
import Definitions.Def_SourceProof_f1f3ffe4516a7a1c4e56daaf
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Protter II.26: raw quadratic variation on finite-variation paths

The actual jump series is obtained from Stieltjes component integrals. The
path-local assertion does not require the FV event to have full measure.
The initial square and all positive-time endpoint jumps are retained.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_996b5538f02fe4ec38c5a73c
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, LocallyBoundedVariationOn (X · ω) univ → ∀ t : ℝ≥0,
      hX.continuousQuadraticVariation hF t ω = 0 := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_f1f3ffe4516a7a1c4e56daaf hX) hF,
    (_root_.Prove2MeSourceProof.h_7a2cd734cad19a873789e942 hX) hF] with ω hq hd hv t
  linarith [(hq hv t), (hd t).2]
end IsSemimartingale

end ProbabilityTheory


